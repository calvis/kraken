#lang racket/base

(provide (all-defined-out))

(require racket/trace (rename-in racket/stream [stream-append stream-append-proc]))

(define-syntax-rule (ignore e ...) (void))

(define-syntax-rule (display/return expr)
  (let ([result expr]) (display " return: ") (display result) (newline) expr))

(define-syntax-rule (stream-append s* ... s)
  (let ([last (lambda () s)]
        [pre (stream-append-proc s* ...)])
    (define (loop stream n)
      (cond
       [(stream-empty? stream) (last)]
       [else (stream-cons (stream-first stream)
                          (loop (stream-rest stream) (add1 n)))]))
    (loop pre 0)))

;; =============================================================================
;; variables

;; normal miniKanren vars are actually an instance of a more general
;; "constrained var", or cvar for short.
(struct cvar (str x) #:transparent)

;; defines a normal miniKanren var as a cvar that is printed with "_"
(struct -var cvar () #:transparent
        #:methods gen:custom-write
        [(define (write-proc x port mode)
           (display (format "#~a(~a)" (cvar-str x) (cvar-x x)) port))])
(define (var x) (-var "_" x))
(define (var? x) (-var? x))
(define var-x cvar-x)

(define (reify-n cvar n)
  (string->symbol (format "~a.~a" (cvar-str cvar) (number->string n))))

;; =============================================================================
;; substitution

(define substitution? list?)

;; the empty association list, abbreviated s
(define empty-s '())
(define empty-s? null?)

(define (ext-s x v s) (cons `(,x . ,v) s))
(define (ext-s* p s) (append p s))

(define (size-s s) (length s))

;; =============================================================================
;; reification

(define (extend-rs v s)
  `((,v . ,(reify-n v (size-s s))) . ,s))

(define (walk/internal u s)
  (cond
   [(and (cvar? u) (assq u s))
    => (lambda (a) (walk/internal (cdr a) s))]
   [(pair? u)
    (cons (walk/internal (car u) s)
          (walk/internal (cdr u) s))]
   [else u]))

(define (reify-s v^ s)
  (define v (walk/internal v^ s))
  (cond
   [(cvar? v)
    (extend-rs v s)]
   [(pair? v) 
    (reify-s (cdr v) (reify-s (car v) s))]
   [else s]))

;; =============================================================================
;; trees

(struct tree (nodes) #:transparent)

;; =============================================================================
;; constraints and attributes

(require racket/class 
         (except-in racket/match ==)
         racket/list
         racket/function
         racket/pretty)

(define base%
  (class* object% (printable<%> equal<%>)
    (super-new)

    (init-field [rator this%] [rands '()]
                [parent #f])

    (define/public (get-rator) this%)
    (define/public (get-rands) rands)

    (define/public (same? obj)
      (and (eq? (send obj get-rator) this%)
           (andmap eq? (send obj get-rands) rands))) ;; TODO: equal?

    (define/public (custom-print p depth)
      (display (cons (object-name this%) rands) p))
    (define/public (custom-write p)
      (write   (cons (object-name this%) rands) p))
    (define/public (custom-display p) 
      (display (cons (object-name this%) rands) p))

    (define/public (equal-to? obj recur?)
      (map recur? rands (get-field rands obj)))

    (define/public (equal-hash-code-of hash-code) 5)
    (define/public (equal-secondary-hash-code-of hash-code) 5)

    (define/public (with-parent p)
      (unless (not parent)
        (error 'with-parent "too many parents"))
      (new this% [rator rator] [rands rands] [parent p]))

    (define ((update-constraints state k) o)
      (if (and (not (subclass? this% conj%))
               (not (subclass? this% disj%))
               (is-a? o functionable%))
          (send o ->out state k) o))

    (define (stream-constraints rands state) 
      (printf "stream-constraints: ~a ~a\n" rands state)
      (cond
       [(or (subclass? this% conj%) (subclass? this% disj%)) state]
       [else
        (for/fold 
          ([state state]) 
          ([o rands] #:when (is-a? o functionable%))
          #:break (not state)
          (send o ->stream state))]))

    (define/pubment (join state)
      (call/cc
       (lambda (k)
         (let ([rands^ (map (update-constraints state k) rands)])
           (cond
            [(ormap (curryr is-a? cdr%) rands^)
             (send state extend (new this% [rands rands^]))]
            [(equal? rands rands^)
             (inner #f join state)]
            [else 
             (send (new this% [rands rands^]) join state)])))))

    (define/pubment (satisfy state)
      (call/cc
       (lambda (k)
         (let ([rands^ (map (update-constraints state k) rands)])
           (cond
            [(ormap (curryr is-a? cdr%) rands^)
             (new this% [rands rands^])]
            [(equal? rands rands^)
             (inner #f satisfy state)]
            [else 
             (send (new this% [rands rands^]) satisfy state)])))))

    ;; State Stream -> Stream
    (define/pubment (augment-stream stream)
      (inner (stream-map (lambda (state) 
                           (cond
                            [(stream-constraints rands state)
                             => (lambda (state) (send this join state))]
                            [else #f]))
                         stream)
             augment-stream stream))))

(define constraint%
  (class base%
    (super-new)
    (define/public (merge c) #f)))

(define succeed%
  (class constraint%
    (super-new)
    (define/augment (join state) state)
    (define/augment (satisfy state) #t)
    (define/override (merge c^) c^)
    (define/augment (augment-stream stream) stream)))

(define succeed 
  (new succeed%))

(define fail%
  (class constraint%
    (super-new)
    (define/augment (join state) #f)
    (define/augment (satisfy state) #f)))

(define fail 
  (new fail%))

(define attribute%
  (class base%
    (super-new)))

(define unary-attribute%
  (class attribute%
    (super-new)
    (inherit-field rator rands)

    (define/augment (join state)
      (or (and (send state get-attribute this% (car rands)) state)
          (inner #f join state)
          (send state set-attribute (new this% [rands rands]))))

    (define/public (get-value) #f)))

(define binary-attribute%
  (class attribute%
    (super-new)

    (inherit-field rator rands)

    (define/augment (join state)
      (inner state join state))))

;; -----------------------------------------------------------------------------
;; conjunction

(define conj%
  (class constraint%
    (super-new)

    (inherit-field [clauses rands])

    (unless (andmap (curryr is-a? base%) clauses)
      (error 'conj% "malformed clauses ~a" clauses))

    (define/augment (join state)
      (for/fold ([state state]) ([constraint clauses])
        (and state (send constraint join state))))

    (define/augment (satisfy state)
      (define result
        (for/fold ([clauses^ '()]) ([c clauses])
          ;; satisfy : State -> False U True U Constraint
          #:break (not clauses^)
          (match (send c satisfy state)
            [#f #f]
            [#t clauses^]
            [c^ (cons c^ clauses^)])))
      (and result (or (null? result) (apply conj (reverse result)))))

    (define/augment (augment-stream stream)
      (let ([stream (send (car clauses) augment-stream stream)]
            [rest   (apply conj (cdr clauses))])
        (send rest augment-stream stream)))))

(define (conj . clauses)
  (cond
   [(null? clauses) succeed]
   [(null? (cdr clauses)) (car clauses)]
   [else (new conj% [rands (reverse
                            (for/fold ([c* '()]) ([c clauses])
                              (if (is-a? c conj%) 
                                  (append (get-field rands c) c*)
                                  (cons c c*))))])]))

;; -----------------------------------------------------------------------------
;; disjunction

(define disj%
  (class constraint%
    (super-new)

    (inherit-field [clauses rands])

    (define/augride (join state)
      (define result
        (for/list ([c clauses]) 
          (and state (send c satisfy state))))
      (cond
       [(findf (curry eq? #t) result) state]
       [else 
        (let ([clauses (filter identity result)])
          (cond
           [(null? clauses) #f]
           [(null? (cdr clauses)) (send (car clauses) join state)]
           [else (send state add-constraint (apply disj clauses))]))]))

    (define/augride (satisfy state)
      (define result
        (for/list ([c clauses]) 
          (and state (send c satisfy state))))
      (cond
       [(findf (curry eq? #t) result) #t]
       [else (apply disj (filter identity result))]))

    (define (stream-interleave stream)
      (let ([stream (stream-filter (compose not stream-empty?) stream)])
        (stream-append
         (stream-map stream-first stream)
         (stream-interleave (stream-map stream-rest stream)))))

    (define/augment (augment-stream stream)
      (stream-interleave (stream-map (lambda (c) (send c augment-stream stream))
                                     clauses)))))

(define (disj #:parent [parent #f] . clauses)
  (cond
   [(null? clauses) fail]
   [(null? (cdr clauses)) 
    (send (car clauses) with-parent parent)]
   [else 
    (define flat-clauses (append-map flatten-disj% clauses))
    (new disj% [rands flat-clauses] [parent parent])]))

(define (flatten-disj% c)
  (cond
   [(is-a? c disj%) (send c get-rands)]
   [else (list c)]))

;; -----------------------------------------------------------------------------
;; not

(define not%
  (class constraint%
    (super-new)

    (inherit-field rands)
    (match-define (list c) rands)))

(define (! c)
  (new not% [rands (list c)]))

;; -----------------------------------------------------------------------------
;; when

(define (when test consequent)
  (new when% [rands (list test consequent)]))

(define when%
  (class constraint%
    (super-new)

    (inherit-field rands)
    (match-define (list test consequent) rands)

    (unless (and (is-a? test base%)
                 (is-a? consequent base%))
      (error 'when "malformed when ~a ~a" test consequent))

    (define/augment (join state)
      (match (send test satisfy state)
        [#f state]
        [#t (send consequent join state)]
        [test^ (send state add-constraint (new when% [rands (list test^ consequent)]))]))

    (define/augment (satisfy state)
      (match (send test satisfy state)
        [#f state]
        [#t (send consequent satisfy state)]
        [test^ (new when% [rands (list test^ consequent)])]))))

;; -----------------------------------------------------------------------------
;; associate

(define (associate x v) 
  (new associate% [rands (list x v)]))

(define (== x v)
  (associate x v))

(define associate%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (match-define (list x v) rands)

    (define/augment (join state)
      (send state associate x v))

    (define/augment (satisfy state)
      (let ([x (send state walk x)]
            [v (send state walk v)])
        (cond
         [(eq? x v) #t]
         [(and (pair? x) (pair? v))
          (send (conj (associate (car x) (car v))
                      (associate (cdr x) (cdr v)))
                satisfy state)]
         [(and (is-a? x functionable%)
               (not (object? v)))
          (send (send x ->rel v) satisfy state)]
         [(and (is-a? v functionable%)
               (not (object? x)))
          (send (send v ->rel x) satisfy state)]
         [(or (var? x) (var? v))
          (associate x v)]
         [else #f])))))

;; -----------------------------------------------------------------------------
;; query

;; nothing here yet

;; =============================================================================
;; state

(define state%
  (class* object% (printable<%> equal<%>)
    (super-new)
    (init-field [s '()] [c succeed] [a '()])

    (define/public (custom-print p depth)
      (display (list 'state% (map (lambda (p) (list (car p) (walk (cdr p)))) s) c a) p))
    (define/public (custom-write p)
      (write   (list 'state% (map (lambda (p) (list (car p) (walk (cdr p)))) s) c a) p))
    (define/public (custom-display p) 
      (display (list 'state% (map (lambda (p) (list (car p) (walk (cdr p)))) s) c a) p))

    (define/public (associate x v)
      (let ([x (walk x)] [v (walk v)])
        (cond
         [(eq? x v) this]
         [(and (is-a? x functionable%)
               (not (object? v)))
          (send x ->rel v this)]
         [(and (is-a? v functionable%)
               (not (object? x)))
          (send v ->rel x this)]
         [(var? x) 
          (let* ([state (new state% [s (cons (cons x v) s)])]
                 [state (join-a a state)]
                 [state (and state (join-c c state))])
            state)]
         [(var? v)
          (let* ([state (new state% [s (cons (cons v x) s)])]
                 [state (join-a a state)]
                 [state (and state (join-c c state))])
            state)]
         [(and (pair? x) (pair? v))
          (let* ([state (send this associate (car x) (car v))]
                 [state (and state (send state associate (cdr x) (cdr v)))])
            state)]
         [(tree? x)
          (tree-associate x v this)]
         [(tree? v)
          (tree-associate v x this)]
         [(equal? x v) this]
         [else #f])))

    (define/public (walk u) (walk/internal u s))

    (define/public (equal-to? obj recur?)
      (and (recur? s (get-field s obj))
           (recur? c (get-field c obj))
           (recur? a (get-field a obj))))

    (define/public (extend obj)
      (cond
       [(is-a? obj attribute%) 
        (set-attribute obj)]
       [else (add-constraint obj)]))

    (define/public (get-attribute x% x)
      (cond
       [(findf (lambda (attr^)
                 (define y% (send attr^ get-rator))
                 (match-define (list y ya ...) (send attr^ get-rands))
                 (and (subclass? x% y%) (eq? x y)))
               a)
        => (lambda (attr^) (send attr^ get-value))]
       [else #f]))

    (define/public (set-attribute attr)
      (define x% (send attr get-rator))
      (match-define (list x xa ...) (send attr get-rands))
      (cond
       [(findf (lambda (attr^)
                 (define y% (send attr^ get-rator))
                 (match-define (list y ya ...) (send attr^ get-rands))
                 (and (subclass? y% x%) (eq? x y)))
               a)
        => (lambda (attr^)
             (or (and (pair? xa)
                      (send (send attr^ merge (car xa))
                            join (new state% [s s] [c c] [a (remq attr^ a)])))
                 this))]
       [(findf (lambda (attr^)
                 (define y% (send attr^ get-rator))
                 (match-define (list y ya ...) (send attr^ get-rands))
                 (and (subclass? x% y%) (eq? x y)))
               a)
        => (lambda (attr^)
             (new state% [s s] [c c] [a (cons attr (remq attr^ a))]))]
       [else (new state% [s s] [c c] [a (cons attr a)])]))

    (define/public (add-constraint c^)
      (unless (is-a? c constraint%)
        (error 'add-constraint "state has non-constraint ~a" c))
      (unless (is-a? c^ constraint%)
        (error 'add-constraint "trying to add non-constraint ~a" c^))
      (define new-c 
        (or (send c merge c^)
            (send c^ merge c)
            (conj c c^)))
      (new this% [s s] [c new-c] [a a]))

    ;; take one state, split it based on the disjunctions in attributes
    (define/public (narrow [n #f])
      (let ([answer-stream (send (apply conj a) augment-stream (list this))])
        (for/list ([i (or n (in-naturals))] [s (stream-filter identity answer-stream)]) s)))

    (define/public (equal-hash-code-of hash-code) 5)
    (define/public (equal-secondary-hash-code-of hash-code) 6)

    ;; ---------------------------------------------------------------------------
    ;; join

    (define/public (join-s s state^)
      (for/fold ([state^ state^]) ([assoc s])
        #:break (not state^)
        (send state^ associate (car assoc) (cdr assoc))))
    
    (define/public (join-c c state^)
      (and c (send c join state^)))

    (define/public (join-a a state^)
      (for/fold ([state^ state^]) ([attr a])
        (and state^ (send attr join state^))))

    ;; State -> [Maybe State]
    (define/public (join state^)
      (let* ([result-state                   (join-s s state^)]
             [result-state (and result-state (join-a a result-state))]
             [result-state (and result-state (join-c c result-state))])
        result-state))

    ;; -------------------------------------------------------------------------
    ;; reify

    (define/public (reify e) 
      (let ([e (walk e)])
        (walk/internal e (reify-s e empty-s))))))

;; t is a tree
(define (tree-associate t v state)
  (cond
   [(not (or (var? v) (tree? v) (pair? v) (null? v))) #f]
   [(null? v)
    (for/fold ([state state]) ([node (tree-nodes t)])
      #:break (not state)
      (send state associate node '()))]
   [else #f]))

(define empty-state (new state%))

;; =============================================================================
;; examples

(define (atomic x) 
  (new atomic% [rands (list x)]))

(define atomic%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (match-define (list x) rands)))

(define (non-atomic x) 
  (! (atomic x)))

(define compound-constraint%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (init-field [partial #f])))

(define !=%
  (class compound-constraint%
    (super-new)
    (inherit-field rands partial)

    (match-define (list x y) rands)))

(define (!= x y)
  (new !=% [rands (list x y)]))

(define (interval? x)
  (pair? x))

(define interval-union
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
                         (jmin (car j)) (jmax (cdr j)))
      (cond
        ((or (= imax jmin)
             (= imax (- jmin 1)))
         `((,imin . ,jmax)))
        ((or (= jmax imin)
             (= jmax (- imin 1)))
         `((,jmin . ,imax)))
        ((< imax jmin) `(,i ,j))
        ((< jmax imin) `(,j ,i))
        ((and (<= imin jmin) (>= imax jmax)) `((,imin . ,imax)))
        ((and (<= jmin imin) (>= jmax imax)) `((,jmin . ,jmax)))
        ((and (<= imin jmin) (>= jmax imax)) `((,imin . ,jmax)))
        ((and (<= jmin imin) (>= imax jmax)) `((,jmin . ,imax)))
        (else (error 'interval-union "not defined for ~a ~a" i j))))))

(define interval-difference
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
                         (jmin (car j)) (jmax (cdr j)))
      (cond
        ((> jmin imax) `((,imin . ,imax)))
        ((and (<= jmin imin) (>= jmax imax)) `())
        ((and (< imin jmin) (> imax jmax))
         `((,imin . ,(- jmin 1)) (,(+ jmax 1) . ,imax)))
        ((and (< imin jmin) (<= jmin imax))
         `((,imin . ,(- jmin 1))))
        ((and (> imax jmax) (<= jmin imin))
         `((,(+ jmax 1) . ,imax)))
        (else (error 'interval-difference "not defined for ~a ~a" i j))))))

(define interval-intersection
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
                         (jmin (car j)) (jmax (cdr j)))
      (cond
        ((< imax jmin) `())
        ((< jmax imin) `())
        ((and (<= imin jmin) (>= imax jmax)) `(,j))
        ((and (<= jmin imin) (>= jmax imax)) `(,i))
        ((and (<= imin jmin) (<= imax jmax))
         `((,jmin . ,imax)))
        ((and (<= jmin imin) (<= jmax imax))
         `((,imin . ,jmax)))
        (else (error 'interval-intersection "not defined for ~a ~a" i j))))))

(define interval-memq?
  (lambda (x intvl)
    (and (>= x (car intvl)) (<= x (cdr intvl)))))

(define interval-combinable?
  (lambda (i j)
    (let ((imin (car i)) (imax (cdr i))
                         (jmin (car j)) (jmax (cdr j)))
      (or (= imax (- jmin 1))
          (= jmax (- imin 1))
          (not (or (> jmin imax) (> imin jmax)))))))

(define interval->
  (lambda (i j)
    (> (car i) (cdr j))))

(define interval-<
  (lambda (i j)
    (< (cdr i) (car j))))

(define singleton-interval?
  (lambda (x)
    (= (car x) (cdr x))))

(define copy-before-interval
  (lambda (pred intvl)
    (let ((min (car intvl)) (max (cdr intvl)))
      (let loop ((i min))
        (cond
          ((pred i)
           (if (= min i) `() `((,min . ,(- i 1)))))
          ((= i max) `())
          (else (loop (+ i 1))))))))

(define drop-before-interval
  (lambda (pred intvl)
    (let ((min (car intvl)) (max (cdr intvl)))
      (let loop ((i min))
        (cond
          ((pred i) `((,i . ,max)))
          ((= i max) `())
          (else (loop (+ i 1))))))))

(define range-dom
  (lambda (lb ub)
    (cond
     [(>= ub 0)
      `((,(max lb 0) . ,ub))]
     [else `()])))

(define value-dom?
  (lambda (v)
    (and (integer? v) (<= 0 v))))

(define make-dom
  (lambda (n*)
    (let loop ((n* n*))
      (cond
        ((null? n*) `())
        (else (cons-dom (car n*) (loop (cdr n*))))))))

(define car-dom
  (lambda (dom)
    (unless (and (list? dom) (andmap interval? dom))
      (error 'car-dom "invalid domain ~a" dom))
    (caar dom)))

(define cdr-dom
  (lambda (dom)
    (unless (and (list? dom) (andmap interval? dom))
      (error 'cdr-dom "invalid domain ~a" dom))
    (let ((intvl (car dom)))
      (if (singleton-interval? intvl)
          (cdr dom)
          (cons `(,(+ (car intvl) 1) . ,(cdr intvl)) (cdr dom))))))

(define cons-dom
  (lambda (x dom)
    (let loop ((x (if (interval? x) x `(,x . ,x))) (dom dom))
      (cond
        ((null-dom? dom) `(,x))
        ((interval-combinable? x (car dom))
         (append-dom (interval-union x (car dom)) (cdr dom)))
        ((interval-> x (car dom))
         (cons-dom (car dom) (loop x (cdr dom))))
        (else (cons x dom))))))

(define append-dom
  (lambda (l s)
    (cond
      ((null-dom? l) s)
      (else (cons-dom (car l) (append-dom (cdr l) s))))))

(define null-dom?
  (lambda (x)
    (null? x)))

(define singleton-dom?
  (lambda (dom)
    (unless (and (list? dom) (andmap interval? dom))
      (error 'singleton-dom? "invalid domain ~a" dom))
    (and (not (null-dom? dom))
         (null-dom? (cdr dom))
         (singleton-interval? (car dom)))))

(define singleton-element-dom
  (lambda (dom)
    (unless (and (list? dom) (andmap interval? dom))
      (error 'singleton-element-dom "invalid domain ~a" dom))
    (caar dom)))

(define min-dom
  (lambda (dom)
    (unless (and (list? dom) (andmap interval? dom))
      (error 'min-dom "invalid domain ~a" dom))
    (caar dom)))

(define max-dom
  (lambda (dom)
    (cond
      ((null-dom? (cdr dom)) (cdar dom))
      (else (max-dom (cdr dom))))))

(define memv-dom?
  (lambda (v dom)
    (and (value-dom? v)
         (findf (lambda (d) (interval-memq? v d)) dom))))

(define intersection-dom
  (lambda (dom1 dom2)
    (cond
      ((or (null-dom? dom1) (null-dom? dom2)) '())
      ((interval-< (car dom1) (car dom2))
       (intersection-dom (cdr dom1) dom2))
      ((interval-> (car dom1) (car dom2))
       (intersection-dom dom1 (cdr dom2)))
      (else
       (let ((a1 (interval-difference (car dom1) (car dom2)))
             (a2 (interval-difference (car dom2) (car dom1))))
         (append-dom
          (interval-intersection (car dom1) (car dom2))
          (intersection-dom
           (append-dom a1 (cdr dom1))
           (append-dom a2 (cdr dom2)))))))))

(define diff-dom
  (lambda (dom1 dom2)
    (cond
      ((or (null-dom? dom1) (null-dom? dom2)) dom1)
      ((interval-< (car dom1) (car dom2))
       (cons (car dom1) (diff-dom (cdr dom1) dom2)))
      ((interval-> (car dom1) (car dom2))
       (diff-dom dom1 (cdr dom2)))
      (else
       (let ((a1 (interval-difference (car dom1) (car dom2)))
             (a2 (interval-difference (car dom2) (car dom1))))
         (diff-dom
          (append-dom a1 (cdr dom1))
          (append-dom a2 (cdr dom2))))))))

(define remq-dom
  (lambda (x dom)
    (diff-dom dom (make-dom (list x)))))

(define copy-before-dom
  (lambda (pred dom)
    (cond
      ((null? dom) '())
      ((let ((intvl (car dom)))
         (and (pred (cdr intvl)) intvl))
       => (lambda (intvl) (copy-before-interval pred intvl)))
      (else (cons (car dom) (copy-before-dom pred (cdr dom)))))))

(define drop-before-dom
  (lambda (pred dom)
    (cond
      ((null? dom) '())
      ((let ((intvl (car dom)))
         (and (pred (cdr intvl)) intvl))
       => (lambda (intvl)
            (append (drop-before-interval pred intvl) (cdr dom))))
      (else (drop-before-dom pred (cdr-dom dom))))))

(define disjoint-dom?
  (lambda (dom1 dom2)
    (cond
      ((or (null? dom1) (null? dom2)) #t)
      ((interval-< (car dom1) (car dom2))
       (disjoint-dom? (cdr dom1) dom2))
      ((interval-> (car dom1) (car dom2))
       (disjoint-dom? dom1 (cdr dom2)))
      (else #f))))

(define dom%
  (class binary-attribute% 
    (super-new)

    (inherit-field rands)
    (define x (car rands))

    (define d 
      (cond
       [(not (null? (cdr rands))) (cadr rands)]
       [(value-dom? x) (range-dom x x)]
       [else (range-dom 0 100)]))
    
    (define/public (get-value) d)

    (define/augment (join state)
      (let ([x (send state walk x)])
        (cond
         [(null-dom? x) #f]
         [(value-dom? x)
          (and (memv-dom? x d) state)]
         [(singleton-dom? d)
          (send state associate x (singleton-element-dom d))]
         [else 
          (send state set-attribute (new dom% [rands (list x d)]))])))

    (define/augment (satisfy state)
      (let ([x (send state walk x)])
        (cond
         [(not (not (memv-dom? x d)))]
         [else 
          (let ([attr^ (send state get-attribute this% x)])
            (let ([i (intersection-dom attr^ d)])
              (or (equal? i attr^) this)))])))

    (define/public (merge d^)
      (define new-d (intersection-dom d d^))
      (new dom% [rands (list x new-d)]))))

(define (dom/a x d)
  (new dom% [rands (list x d)]))

(define (+fd . n*)
  (cond
   [(or (null? n*) (null? (cdr n*))) 
    succeed]
   [(null? (cddr n*)) 
    (associate (car n*) (cadr n*))]
   [(null? (cdddr n*))
    (new +fd% [rands n*])]
   [else
    (match-define (list n1 n2 rest ...) n*)
    (let ([n^ (var (gensym 'n))])
      (conj (+fd n1 n2 n^)
            (apply +fd (cons n^ rest))))]))

(define functionable% (interface () ->out ->rel ->stream))

(define +fd%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (match-define (list u v w) rands)

    ;; KEEP PUTTING IT IN until the attributes it is trying to assign
    ;; are TRIVIALLY TRUE
    (define/augment (join state)
      (let ([u (send state walk u)]
            [v (send state walk v)]
            [w (send state walk w)])
        (let ([du (or (send state get-attribute dom% u) 
                      (and (value-dom? u) (range-dom u u))
                      (range-dom 0 100))]
              [dv (or (send state get-attribute dom% v) 
                      (and (value-dom? v) (range-dom v v))
                      (range-dom 0 100))]
              [dw (or (send state get-attribute dom% w) 
                      (and (value-dom? w) (range-dom w w))
                      (range-dom 0 100))])
          (let ([wmin (min-dom dw)] [wmax (max-dom dw)]
                [umin (min-dom du)] [umax (max-dom du)]
                [vmin (min-dom dv)] [vmax (max-dom dv)])
            (let ([new-w-dom (range-dom (+ umin vmin) (+ umax vmax))]
                  [new-u-dom (range-dom (- wmin vmax) (- wmax vmin))]
                  [new-v-dom (range-dom (- wmin umax) (- wmax umin))])
              (cond
               [(or (var? u) (var? v) (var? w))
                (let* ([state            (send state add-constraint (+fd u v w))]
                       [state (and state (send (dom/a u new-u-dom) join state))]
                       [state (and state (send (dom/a v new-v-dom) join state))]
                       [state (and state (send (dom/a w new-w-dom) join state))])
                  state)]
               [else state]))))))))

(define tree%
  (class unary-attribute%
    (super-new)

    (inherit-field rands)

    (define/augride (join state)
      (let ([t (send state walk (car rands))])
        (cond
         [(list? t) (send (list/a t) join state)]
         [(send state get-attribute list% t) state]
         [(tree? t)
          (match-define (tree nodes) t)
          (and (list? nodes)
               (for/fold ([state state]) ([node nodes])
                 #:break (not state)
                 (send (list/a node) join state)))]
         [else #f])))

    (define/augride (augment-stream stream) 
      (stream-map (lambda (state) (send this join state)) stream))

    (define/augride (satisfy state)
      (let ([t (send state walk (car rands))])
        (or (tree? t) (list? t) (tree/a t))))))

(define (tree/a t)
  (new tree% [rands (list t)]))

(define list%
  (class tree%
    (super-new)

    (init-field [body #f])

    (unless (or (not body) (is-a? body base%))
      (error 'list% "malformed body ~a" body))
    
    (inherit-field rands)
    (define ls (car rands))

    (define (init-body)
      (disj (associate ls `())
            (list/a (@ (cdr/o ls)))))
    
    (define/override (join state)
      (match (send (or body (init-body)) satisfy state)
        [#f #f]
        [#t state]
        [c^ (send state set-attribute (new list% [rands rands] [body c^]))]))

    (define/override (satisfy state)
      (match (send (or body (init-body)) satisfy state)
        [#f #f]
        [#t #t]
        [c^ (new list% [rands rands] [body c^])]))

    (define/override (augment-stream stream)
      (send (or body (init-body)) augment-stream stream))))

(define (list/a ls)
  (new list% [rands (list ls)]))

(define length%
  (class binary-attribute%
    (super-new)

    (inherit-field rands)
    (define x (car rands))
    (define n
      (cond
       [(not (null? (cdr rands))) (cadr rands)]
       [(list? x) (length x)]
       [else (range-dom 0 100)]))

    ;; this should be written with Racket because the idea is to make
    ;; calculating length fast; length does no enumeration itself
    (define/augment (join state)
      (let ([x (send state walk x)]
            [n (send state walk n)])
        (cond
         [(send state get-attribute this% x)
          ;; if there's already a length attribute, then set the new
          ;; length equal to the one that was already there
          => (lambda (n^) (send state associate n n^))]
         [(send (tree/a x) join state)
          => (lambda (state)
               (cond
                [(and (list? x) (number? n))
                 (and (= (length x) n) state)]
                [(and (tree? x) (number? n))
                 (define n* (for/list ([node (tree-nodes x)])
                              (var (gensym 'n))))
                 (send (apply conj 
                              (apply +fd (append n* (list n)))
                              (for/list ([node (tree-nodes x)] [n n*])
                                (length/a node n)))
                       join state)]
                [(number? n)
                 (send state associate x (for/list ([i n]) (var 'n)))]
                [(and (list? x) (var? n))
                 (send state associate n (length x))]
                [(and (list? x) (pair? n))
                 (and (memv-dom? x n) state)]
                [(pair? x)
                 (send (length/a (cdr x) (sub1/o n)) join state)]
                [(null? x)
                 (send state associate n 0)]
                [else (send state set-attribute (length/a x n))]))]
         [else #f])))

    (define/public (get-value) n)))

(define (length/a x n)
  (new length% [rands (list x n)]))

(define (run constraint [n #f])
  (unless (is-a? constraint base%)
    (error 'run "not given a constraint; ~a" constraint))
  (cond
   [(send constraint join empty-state)
    => (lambda (state) (send state narrow n))]
   [else '()]))

(define cdr%
  (class* constraint% (functionable%)
    (super-new)
    (inherit-field rands)

    (define ls (car rands))

    (define/public (->out state k)
      (let ([ls (send state walk ls)])
        (cond
         [(pair? ls) (cdr ls)]
         [(object? ls)
          (let ([ls (send ls ->out state k)])
            (cond
             [(pair? ls) (cdr ls)]
             [(not (or (var? ls) (object? ls))) (k #f)]
             [else (new cdr% [rands (list ls)])]))]
         [(not (var? ls)) (k #f)]
         [else (new cdr% [rands (list ls)])])))

    (define/public (->rel v state)
      (let ([ls (send state walk ls)])
        (cond
         [(object? ls)
          (let ([lso (var 'lso)])
            (let ([state (send ls ->rel lso state)])
              (send state add-constraint (new this% [rands (list lso v)]))))]
         [else (send (cdr/o ls v) join state)])))

    (define/public (->stream state)
      (let ([ls (send state walk ls)])
        (printf "cdr%: ~a ~a\n" ls state)
        (cond
         [(pair? ls) state]
         [else
          (let ([a (var (gensym 'a))] [d (var (gensym 'd))])
            (send state associate (cons a d) (car rands)))])))
    
    (define/augment (join state)
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) 
          (send state associate (cdr ls) out)]
         [(null? out) 
          (let ([a (var 'a)])
            (send state associate (list a) ls))]
         [else (send state add-constraint (cdr/o ls out))])))))

(define (cdr/c . rands)
  (new cdr% [rands rands]))
(define cdr/o cdr/c)

(define sub1/o
  (case-lambda
   [(n) (+fd n 1)]
   [(n m) (+fd n 1 m)]))

(define (@ c) c)
