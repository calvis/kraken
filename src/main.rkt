#lang racket/base

(provide (all-defined-out))

(require racket/trace racket/stream)

(define-syntax-rule (ignore e ...) (void))

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

;; =============================================================================
;; trees

(struct tree (nodes) #:transparent)

;; =============================================================================
;; constraints and attributes

(require racket/class 
         racket/match
         (except-in racket/list range take)
         racket/function
         racket/pretty)

(define base%
  (class* object% (printable<%> equal<%>)
    (super-new)

    (init-field [rator this%] [rands '()])

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
    (define/public (equal-secondary-hash-code-of hash-code) 5)))

(define reifiable<%>
  (interface () reify))

(define default-reify
  (mixin () (reifiable<%>)
         (inherit-field rands)
         (define/public (reify)
           (cons (object-name this%) rands))))

(define (ext-a attr a)
  (define x% (get-field rator attr))
  (define x  (car (get-field rands attr)))
  (cond
   [(findf (lambda (obj) 
             (define y% (send obj get-rator))
             (define y  (car (get-field rands attr)))
             (and (subclass? y% x%) (eq? y x)))
           a)
    => (lambda (attr^) (cons (send attr^ join attr) (remq attr^ a)))]
   [else (cons attr a)]))
(require racket/trace) (trace ext-a)

(define constraint%
  (class base%
    (super-new)

    (define/public (merge c) #f)))

(define succeed%
  (class constraint%
    (super-new)
    (define/public (join state) state)
    (define/public (satisfy state) #t)
    (define/override (merge c^) c^)))

(define succeed 
  (new succeed%))

(define fail%
  (class constraint%
    (super-new)
    (define/public (join state) #f)
    (define/public (satisfy state) #f)))

(define fail 
  (new fail%))

(define reifiable-constraint%
  (default-reify constraint%))

(define attribute%
  (class base%
    (super-new)

    (inherit-field rator rands)

    (define/pubment (join state)
      (let ([a^ (send state get-attribute this% (car rands))])
        (cond
         [(equal? (cadr rands) a^) state]
         [else (inner #f join state)])))))

;; -----------------------------------------------------------------------------
;; conjunction

(define conj%
  (class constraint%
    (super-new)

    (inherit-field [clauses rands])

    (unless (andmap (curryr is-a? constraint%) clauses)
      (error 'conj% "malformed clauses ~a" clauses))

    (define/public (join state)
      (for/fold ([state state]) ([constraint clauses])
        (and state (send constraint join state))))

    (define/public (satisfy state)
      (define result
        (for/fold ([clauses^ '()]) ([c clauses])
          ;; satisfy : State -> False U True U Constraint
          #:break (not clauses^)
          (match (send c satisfy state)
            [#f #f]
            [#t clauses^]
            [c^ (cons c^ clauses^)])))
      (or (not result) (apply conj (reverse result))))))

(define (conj . clauses)
  (cond
   [(null? clauses) succeed]
   [(null? (cdr clauses)) (car clauses)]
   [else (new conj% [rands clauses])]))

;; -----------------------------------------------------------------------------
;; disjunction

(define disj%
  (class constraint%
    (super-new)

    (inherit-field [clauses rands])

    (define/public (join state^)
      (define result
        (for/list ([state clauses]) 
          (and state state^ (send state satisfy state^))))
      (cond
       [(findf (curry eq? #t) result) state^]
       [else 
        (let ([clauses (filter identity result)])
          (cond
           [(null? clauses) #f]
           [(null? (cdr clauses))
            (define (satisfy->join state)
              (define s (get-field s state))
              (define c (get-field c state))
              (define a (get-field a state))
              (new state%
                   [s (if (boolean? s) '() s)]
                   [c (if (boolean? c) succeed c)]
                   [a (if (boolean? a) '() a)]))
            (send (satisfy->join (car clauses)) join state^)]
           [else (send state^ add-constraint (apply disj clauses))]))]))))

(define (disj . clauses)
  (cond
   [(null? clauses) #f]
   [(null? (cdr clauses)) 
    (define (satisfy->join state)
      (define s (get-field s state))
      (define c (get-field c state))
      (define a (get-field a state))
      (new state%
           [s (if (boolean? s) '() s)]
           [c (if (boolean? c) succeed c)]
           [a (if (boolean? a) '() a)]))
    (satisfy->join (car clauses))]
   [else 
    (define flat-clauses (append-map flatten-disj% clauses))
    (new state% 
         [s `()]
         [c (new disj% [rands flat-clauses])]
         [a `()])]))

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

    (unless (and (is-a? test constraint%)
                 (is-a? consequent constraint%))
      (error 'when "malformed when ~a ~a" test consequent))

    (define/public (join state)
      (match (send test satisfy state)
        [#f state]
        [#t (send consequent join state)]
        [test^ (send state add-constraint (new when% [rands (list test^ consequent)]))]))))

;; -----------------------------------------------------------------------------
;; associate

(define (associate x v) 
  (new associate% [rands (list x v)]))

(define associate%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (match-define (list x v) rands)

    (define/public (join state)
      (send state associate x v))

    (define/public (satisfy state)
      (let ([x (send state walk x)]
            [v (send state walk v)])
        (cond
         [(eq? x v) #t]
         [(or (pair? x) (pair? v))
          (send (conj (associate (car x) (car v))
                      (associate (cdr x) (cdr v)))
                satisfy state)]
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
      (display (list 'state% s c a) p))
    (define/public (custom-write p)
      (write   (list 'state% s c a) p))
    (define/public (custom-display p) 
      (display (list 'state% s c a) p))

    (define/public (associate x v)
      (let ([x (walk x)] [v (walk v)])
        (cond
         [(eq? x v) this]
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
         [(equal? x v) this]
         [else #f])))

    (define/public (walk u) (walk/internal u s))

    (define (walk/internal u s)
      (cond
       [(and (cvar? u) (assq u s))
        => (lambda (a) (walk/internal (cdr a) s))]
       [else u]))

    (define/public (equal-to? obj recur?)
      (and (recur? s (get-field s obj))
           (recur? c (get-field c obj))
           (recur? a (get-field a obj))))

    (define/public (get-attribute x% x)
      (cond
       [(findf (lambda (attr^)
                 (define y% (send attr^ get-rator))
                 (match-define (list y ya) (send attr^ get-rands))
                 (and (subclass? x% y%) (eq? x y)))
               a)
        => (lambda (attr^) (send attr^ get-value))]
       [else (send (new x% [rands (list x)]) get-value)]))

    (define/public (set-attribute attr)
      (define x% (send attr get-rator))
      (match-define (list x xa) (send attr get-rands))
      (cond
       [(findf (lambda (attr^)
                 (define y% (send attr^ get-rator))
                 (match-define (list y ya) (send attr^ get-rands))
                 (and (subclass? x% y%) (eq? x y)))
               a)
        => (lambda (attr^)
             (send (send attr^ merge xa)
                   join (new state% [s s] [c c] [a (remq attr^ a)])))]
       [else (new state% [s s] [c c] [a (cons attr a)])]))

    (define/public (add-constraint c^)
      (unless (is-a? c^ constraint%)
        (error 'add-constraint "trying to add non-constraint ~a" c^))
      (define new-c 
        (or (send c merge c^)
            (send c^ merge c)
            (conj c c^)))
      (new this% [s s] [c new-c] [a a]))

    ;; take one state, split it based on the disjunctions in attributes
    (define/public (to-stream)
      (cond
       [(null? a) (list this)]
       [else (apply stream-append (map (lambda (a) (send a to-stream this)) a))]))

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
        ;; (printf "join:\n 1: ~a\n 2: ~a\n 3: ~a\n" this state^ result-state)
        result-state))

    ;; ---------------------------------------------------------------------------
    ;; satisfy

    (define/public (satisfy-s s state^)
      (define new-s
        (for/fold ([s^ '()]) ([assoc s])
          #:break (not s^)
          ;; check if x is associated to the same thing in the other state
          (define x (car assoc))
          (define u (walk (cdr assoc)))
          (define v (send state^ walk x))
          (cond
           [(eq? u v) s^]
           [(or (var? v) (var? u)) (cons (cons v u) s^)]
           [else #f])))
      (or (null? new-s) new-s))

    (define/public (satisfy-a a state^)
      (define new-a
        (for/fold ([a^ '()]) ([attr a])
          #:break (not a^)
          (cond
           [(send attr satisfy state^)
            => (lambda (attr^)
                 (cond
                  [(boolean? attr^) a^]
                  [else (cons attr^ a^)]))]
           [else #f])))
      (or (null? new-a) new-a))

    (define/public (satisfy-c c state^)
      (send c satisfy state^))

    ;; State -> False U True U State
    (define/public (satisfy state^)
      (let* ([s^ (or (boolean? s) (satisfy-s s state^))]
             [a^ (or (boolean? a) (satisfy-a a state^))]
             [c^ (or (boolean? c) (satisfy-c c state^))])
        (and s^ a^ c^
             (or (andmap boolean? (list s^ a^ c^))
                 (new state% [s s^] [c c^] [a a^])))))))

(define empty-state (new state%))

(define attribute-update-state%
  (class state%
    (super-new)

    (inherit-field s c a)
    (inherit join-a join-c join-s
             satisfy-a satisfy-c satisfy-s)

    ;; if we can update the substitution and the attributes without
    ;; changing anything, then don't add the constraint
    (define/override (join state^)
      (let* ([result-state (join-s s state^)]
             [a^ (satisfy-a a result-state)])
        ;; (printf "join:\n 1: ~a\n 2: ~a\n" this state^)
        (cond
         [(boolean? a^)
          ;; (printf " (attribute ~a was satsified)\n 3: ~a\n"
          ;;         result-state a)
          result-state]
         [else 
          ;; (printf " (attribute ~a not satisfied in ~a)\n" a^ result-state)
          (let* ([result-state (and result-state a^ (join-a a^ result-state))]
                 [result-state (and result-state    (join-c c result-state))])
            ;; (printf " 3: ~a\n" result-state)
            result-state)])))))

;; =============================================================================
;; take

(define (take state [n #f])
  (cond
   [state (for/list ([s (send state to-stream)]
                     [i (or n (in-naturals))])
            s)]
   [else '()]))

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

(define (reify c) c)

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

(define range
  (lambda (lb ub)
    `((,lb . ,ub))))

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
    (and (null-dom? (cdr dom))
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
  (class attribute% 
    (super-new)

    (inherit-field rands)
    (define x (car rands))

    (define d 
      (cond
       [(not (null? (cdr rands))) (cadr rands)]
       [(value-dom? x) (range x x)]
       [else (range 0 100)]))
    
    (define/public (get-value) d)

    (define/augment (join state)
      (let ([x (send state walk x)])
        (cond
         [(value-dom? x)
          (and (memv-dom? x d) state)]
         [(singleton-dom? d)
          (send state associate x (singleton-element-dom d))]
         [else 
          (send state set-attribute (new dom% [rands (list x d)]))])))

    (define/public (satisfy state)
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

(define (dom x d)
  (send (new dom% [rands (list x d)]) join empty-state))

(define (+fd . n*)
  (cond
   [(or (null? n*) (null? (cdr n*))) empty-state]
   [(null? (cddr n*)) (associate (car n*) (cadr n*))]
   [(null? (cdddr n*))
    (send (new +fd% [rands n*]) join empty-state)]
   [else
    (match-define (list n1 n2 rest ...) n*)
    (let ([n^ (var (gensym 'n))])
      (conj (+fd n1 n2 n^)
            (apply +fd (cons n^ rest))))]))

(define +fd%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (match-define (list u v w) rands)

    ;; KEEP PUTTING IT IN until the attributes it is trying to assign
    ;; are TRIVIALLY TRUE
    (define/public (join state)
      (let ([u (send state walk u)]
            [v (send state walk v)]
            [w (send state walk w)])
        (let ([du (send state get-attribute dom% u)]
              [dv (send state get-attribute dom% v)]
              [dw (send state get-attribute dom% w)])
          (let ([wmin (min-dom dw)] [wmax (max-dom dw)]
                [umin (min-dom du)] [umax (max-dom du)]
                [vmin (min-dom dv)] [vmax (max-dom dv)])
            (let ([new-w-dom (range (+ umin vmin) (+ umax vmax))]
                  [new-u-dom (range (- wmin vmax) (- wmax vmin))]
                  [new-v-dom (range (- wmin umax) (- wmax umin))])
              (send (new attribute-update-state%
                         [s `()]
                         [c (new +fd% [rands (list u v w)])]
                         [a `(,(new dom% [rands (list u new-u-dom)])
                              ,(new dom% [rands (list v new-v-dom)])
                              ,(new dom% [rands (list w new-w-dom)]))])
                    join state))))))))

(define list%
  (class attribute%
    (super-new)
    (inherit-field rands)
    (define ls (car rands))

    (define/augment (join state)
      (disj (associate ls `())
            (let ([a (var 'a)] [d (var 'd)])
              (when (associate (cons a d) ls)
                (list/a d)))))))

(define (list/a ls)
  (send (new list% [rands (list ls)]) join empty-state))

(define length%
  (class attribute%
    (super-new)

    (inherit-field rands)
    (define x (car rands))
    (define n
      (cond
       [(not (null? (cdr rands))) (cadr rands)]
       [(list? x) (length x)]
       [else (range 0 100)]))

    (define/public (get-value) n)

    (define/augment (join state)
      (let ([x (send state walk x)]
            [n (send state walk n)])
        #;
        (cond
         [(and (list? x) (number? n))
          (and (= (length x) n) state)]
         [(list? x)
          (send state associate n (length x))]
         [(tree? x)
          (match-define (tree nodes) x)
          (define n* (for/list ([node nodes]) (var (gensym 'n))))
          (let* ([state (for/fold ([state state]) ([node nodes] [n n*])
                          (and state (send state set-attribute (new length% [rands (list node n)]))))]
                 [state^ (apply +fd (append n* (list n)))])
            (and state^ (send state^ join state)))]
         [(number? n)
          (send state associate x (for/list ([i n]) (var 'n)))]
         [else (send state set-attribute (new length% [rands (list x n)]))])

        (printf "length: ~a ~a\n" this state)
        (let ([state^ (disj
                       (conj (associate n 0)
                             (associate x `()))
                       (let ([n^ (var (gensym 'n))] [a (var 'a)] [d (var 'd)])
                         (when (associate (cons a d) x)
                           (conj 
                            (+fd n^ 1 n)
                            (new length% [rands (list d n^)])
                            ))))])
          (and state^ (send state^ join state)))))))

(define (length/a x n)
  (send (new length% [rands (list x n)]) join empty-state))

(define tree-unify%
  (class constraint%
    (super-new)
    (inherit-field rands)

    (define/public (join state)
      (let ([t (send state walk (car rands))]
            [v (send state walk (cadr rands))])
        (cond
         [(not (var? v))
          (verify-tree t v state)]
         [else
          (match-define (tree nodes) t)
          (cond
           [(null? nodes) 
            (send state associate v `())]
           [(pair? (first nodes))
            (let ([a (var (gensym 'a))] [d (var (gensym 'd))])
              (let* ([state (send state associate (cons a d) v)]
                     [state (and state (send state associate (caar nodes) a))])
                (and state
                     (send (new tree-unify% [rands (list d (tree (cons (cdar nodes) (cdr nodes))))])
                           join state))))]
           [else (send state add-constraint (new tree-unify% [rands (list t v)]))])])))

    (define (verify-tree t v state) ;; v is not a var
      (match-define (tree nodes) t)
      (cond
       [(null? v)
        (send (apply conj (for/list ([node nodes]) (associate node `())))
              join state)]
       [(pair? v)
        (send (conj (new tree-first% [rands (list t (car v))])
                    (new tree-rest%  [rands (list t (cdr v))]))
              join state)]
       [else #f]))))

(define (tree-unify t v)
  (let ([n (var (gensym 'n))])
    (conj (length/a t n)
          (length/a v n)
          (new tree-unify% [rands (list t v)]))))

(define tree-first%
  (class constraint%
    (super-new)
    (inherit-field rands)

    (define/public (join state)
      (let ([t (send state walk (car rands))]
            [v (send state walk (cadr rands))])
        (match-define (tree nodes) t)
        (cond
         [(pair? (first nodes))
          (send state associate v (caar nodes))]
         [else (send state add-constraint (new this% [rands (list t v)]))])))))

(define tree-rest%
  (class constraint%
    (super-new)
    (inherit-field rands)

    (define/public (join state)
      (let ([t (send state walk (car rands))]
            [v (send state walk (cadr rands))])
        (match-define (tree nodes) t)
        (cond
         [(null? nodes) #f]
         [(pair? (first nodes))
          (send (new tree-unify% [rands (list (tree (cons (cdar nodes) (cdr nodes))) v)])
                join state)]
         [else (send state add-constraint (new this% [rands (list t v)]))])))))

(define (run constraint)
  (unless (is-a? constraint constraint%)
    (error 'run "not given a constraint; ~a" constraint))
  (take (send constraint join empty-state)))
