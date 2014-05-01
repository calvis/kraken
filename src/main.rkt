#lang racket/base

(provide (all-defined-out))

(require (rename-in racket/stream [stream-append stream-append-proc]))

(define-syntax-rule (ignore e ...) (void))

(define-syntax-rule (display/return expr)
  (let ([result expr]) (display " return: ") (display result) (newline) expr))

(define-syntax-rule (stream-append s* ... s)
  (let ([last (lambda () s)]
        [pre (stream-append-proc s* ...)])
    (define (loop stream)
      (cond
       [(stream-empty? stream) (last)]
       [else (stream-cons (stream-first stream) (loop (stream-rest stream)))]))
    (loop pre)))

(define (stream-interleave stream)
  (cond
   [(stream-empty? stream) stream]
   [else
    (let ([stream (stream-filter (compose not stream-empty?) stream)])
      (stream-filter
       (compose not (curryr is-a? fail%))
       (stream-append
        (stream-map stream-first stream)
        (stream-interleave (stream-map stream-rest stream)))))]))

(define ((update-constraints state k bad) o)
  (if (is-a? o functionable%) (send o ->out state k bad) o))

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
   [(tree? u)
    (tree (map (curryr walk/internal s) (tree-nodes u)))]
   [else u]))

(define (reify-s v^ s)
  (define v (walk/internal v^ s))
  (cond
   [(cvar? v)
    (extend-rs v s)]
   [(pair? v) 
    (reify-s (cdr v) (reify-s (car v) s))]
   [(tree? v)
    (for/fold ([s s]) ([node (tree-nodes v)])
      (reify-s node s))]
   [else s]))

;; =============================================================================
;; trees

(struct tree (nodes) #:transparent
        #:methods gen:custom-write
        [(define (write-proc x port mode)
           (display
            (for/fold ([nodes '()]) ([node (tree-nodes x)])
              (cond
               [(list? node) (append nodes node)]
               [else (append nodes (list '@ node))]))
            port))])

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

    (init-field [rator this%] [rands '()])

    (define/public (get-rator) this%)
    (define/public (get-rands) rands)

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

    (define/public (update-rands rands)
      (new this% [rands rands]))

    (define/pubment (join state)
      (call/cc
       (lambda (k)
         (let ([rands^ (map (update-constraints state k fail) rands)])
           (cond
            [(and (ormap (curryr is-a? delay%) rands^)
                  (not (is-a? this ==%)))
             (send state add (send this update-rands rands^))]
            [(and (findf (curryr is-a? functionable%) rands^))
             (define-values (new-state new-rands)
               (for/fold ([state state] [rands '()]) ([r rands^])
                 (cond
                  [(is-a? r functionable%)
                   (let ([out (var (gensym 'out))])
                     (values (send r ->rel out state)
                             (cons out rands)))]
                  [else (values state (cons r rands))])))
             (send (send this update-rands (reverse new-rands)) join new-state)]
            [(map eq? rands rands^)
             (inner state join state)]
            [else 
             (send (send this update-rands rands^) join state)])))))

    (define/pubment (satisfy state)
      (call/cc
       (lambda (k)
         (let ([rands^ (map (update-constraints state k #f) rands)])
           (cond
            [(ormap (curryr is-a? delay%) rands^)
             (send this update-rands rands^)]
            [(equal? rands rands^)
             (inner #f satisfy state)]
            [else 
             (send (send this update-rands rands^) satisfy state)])))))

    (define (force-delays stream)
      (let ([rands (filter (curryr is-a? functionable%) rands)])
        (for/fold ([stream stream]) ([r rands])
          (send r augment-stream stream))))

    ;; State Stream -> Stream
    (define/pubment (augment-stream stream)
      (printf "augment-stream: ~a\n" this)
      (inner (stream-filter
              (compose not (curryr is-a? fail%))
              (stream-map (lambda (state) (send this join state))
                          (force-delays stream)))
             augment-stream stream))))

(define constraint% 
  (class base%
    (super-new)))

(define attribute%
  (class base%
    (super-new)
    (inherit-field rands)

    (define/public (same-as? x% x)
      (and (eq? x (car rands)) 
           (or (implementation? x% (class->interface this%))
               (implementation? this% (class->interface x%)))))))

(define unary-attribute%
  (class attribute% 
    (super-new)
    (define/public (merge a state)
      (cond
       [(implementation? (send a get-rator) (class->interface this%))
        (send state set-attribute a)]
       [else (send state set-attribute this)]))))

(define binary-attribute%
  (class attribute% (super-new)))

;; -----------------------------------------------------------------------------
;; not

(define (! c) c)

;; -----------------------------------------------------------------------------
;; associate

(define (== x v)
  (new ==% [rands (list x v)]))

(define ==%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (match-define (list x v) rands)

    (define/augment (join state)
      (send state associate x v))

    (define/augment (satisfy state)
      (send state associate x v))))

;; =============================================================================
;; states

(define state%
  (class* object% (equal<%> printable<%>)
    (super-new)

    (init-field [s '()] [c '()] [a '()])

    (define/public (equal-to? obj recur?)
      (and (recur? s (get-field s obj))
           (recur? c (get-field c obj))
           (recur? a (get-field a obj))))

    (define/public (equal-hash-code-of hash-code) 5)
    (define/public (equal-secondary-hash-code-of hash-code) 5)

    (define/public (walk u) (walk/internal u s))

    (define/public (custom-print p depth)
      (display (list (object-name this%)
                     (map (lambda (p) (list (car p) (walk (cdr p)))) s) c a) p))
    (define/public (custom-write p)
      (write   (list (object-name this%)
                     (map (lambda (p) (list (car p) (walk (cdr p)))) s) c a) p))
    (define/public (custom-display p) 
      (display (list (object-name this%)
                     (map (lambda (p) (list (car p) (walk (cdr p)))) s) c a) p))

    (define/public (get-attribute x% x)
      (cond
       [(findf (lambda (a) (send a same-as? x% x)) a)
        => (lambda (a) (send a get-value))]
       [else #f]))

    (define/public (has-attribute x% x)
      (findf (lambda (a) (send a same-as? x% x)) a))

    (define/public (set-attribute attr)
      (define x% (send attr get-rator))
      (define x  (car (send attr get-rands)))
      (cond
       [(findf (lambda (a) (send a same-as? x% x)) a)
        => (lambda (attr^) 
             (send attr merge attr^ (new this% [s s] [c c] [a (remq attr^ a)])))]
       [else (new this% [s s] [c c] [a (cons attr a)])]))

    (define/public (join-s s)
      (for/fold ([state this]) ([p s])
        (send state associate (car p) (cdr p))))

    (define/public (join-a a)
      (for/fold ([state this]) ([attribute a])
        (send attribute join state)))

    (define/public (join-c c)
      (for/fold ([state this]) ([constraint c])
        (send constraint join state)))
    
    ;; Substitution -> (False U True U Substitution)
    ;; does this satisfy all the bindings in s
    (define/public (satisfy-s s)
      (for/fold ([s '()]) ([p s])
        #:break (not s)
        (cond [(satisfy-p p) => (curryr append s)] [else #f])))

    ;; Association -> [List-of Association]
    (define (satisfy-p p)
      (let ([x (walk (car p))] [v (walk (cdr p))])
        (cond
         [(eq? x v) (list)]
         [(var? x) (list (cons x v))]
         [(var? v) (list (cons v x))]
         [else #f])))

    ;; [List-of Attribute] -> [Maybe [List-of Attribute]]
    (define/public (satisfy-a a)
      (for/fold ([a '()]) ([attribute a])
        #:break (not a)
        (match (send attribute satisfy this)
          [#t a] [#f #f] [a^ (cons a^ a)])))

    ;; [List-of Constraint] -> [Maybe [List-of Constraint]]
    (define/public (satisfy-c c)
      (for/fold ([c '()]) ([constraint c])
        #:break (not c)
        (match (send constraint satisfy this)
          [#t c] [#f #f] [c^ (cons c^ c)])))
    
    (define/public (add x)
      (cond
       [(is-a? x constraint%)
        (add-constraint x)]
       [else (set-attribute x)]))

    (define/public (add-constraint c^)
      (new this% [s s] [c (cons c^ c)] [a a]))

    (define/public (join state)
      (send+ state (join-s s) (join-c a) (join-c c)))

    ;; State -> (False U True U State)
    (define/public (satisfy state)
      (cond
       [(send state satisfy-s s)
        => (lambda (s)
             (cond
              [(send state satisfy-a a)
               => (lambda (a)
                    (cond
                     [(send state satisfy-c c)
                      => (lambda (c)
                           (or (andmap null? (list s c a))
                               (new this% [s s] [c c] [a a])))]
                     [else #f]))]
              [else #f]))]
       [else #f]))

    (define/public (narrow [n #f])
      (define (take stream n)
        (cond
         [(and n (zero? n)) '()]
         [(stream-empty? stream) '()]
         [else (cons (stream-first stream) 
                     (take (stream-rest stream) (and n (sub1 n))))]))
      (printf "narrowing: ~a\n" this)
      (define answer-stream
        (send this augment-stream (list (new join%))))
      (take (stream-filter (compose not (curryr is-a? fail%)) answer-stream) n))

    (define/public (reify v)
      (let ([v (walk v)])
        (walk/internal v (reify-s v '()))))))

(define join%
  (class state%
    (super-new)
    (inherit walk)
    (inherit-field s c a)

    (define/public (associate x v)
      (let ([x (walk x)] [v (walk v)])
        (cond
         [(eq? x v) this]
         [(and (is-a? x delay%) (not (object? v)))
          (send x ->rel v this)]
         [(and (is-a? v delay%) (not (object? x)))
          (send v ->rel x this)]
         [(var? x) 
          (send (new this% [s (cons (cons x v) s)] [c c] [a a])
                update (cons x v))]
         [(var? v)
          (send (new this% [s (cons (cons v x) s)] [c c] [a a])
                update (cons v x))]
         [(and (pair? x) (pair? v))
          (send (associate (car x) (car v)) associate (cdr x) (cdr v))]
         [(tree? x)
          (tree-associate x v this)]
         [(tree? v)
          (tree-associate v x this)]
         [(equal? x v) this]
         [else (new fail%)])))

    (define/public (augment-stream stream)
      (stream-filter
       (compose not (curryr is-a? fail%))
       (let ([stream (stream-map (lambda (state) (send state join-s s)) stream)])
         (for/fold ([stream stream]) ([thing (append c a)])
           (send thing augment-stream stream)))))

    (define/public (update pair)
      (send (send (new this% [s s]) join-a a) join-c c))))

(define satisfy%
  (class state%
    (super-new)
    (inherit walk)
    (inherit-field s c a)

    (define/public (associate x v)
      (let ([x (walk x)] [v (walk v)])
        (cond
         [(eq? x v) #t]
         [(var? x) 
          (new this% [s (cons (cons x v) s)] [c c] [a a])]
         [(var? v)
          (new this% [s (cons (cons v x) s)] [c c] [a a])]
         [(and (pair? x) (pair? v))
          (match (associate (car x) (car v))
            [#t (associate (cdr x) (cdr v))]
            [#f #f]
            [state^ (match (send state^ associate (cdr x) (cdr v))
                      [#t state^]
                      [#f #f]
                      [state^^ state^^])])]
         [(equal? x v) #t]
         [else #f])))

    (define/public (augment-stream stream)
      (send (new join% [s s] [c c] [a a]) augment-stream stream))))

(define fail%
  (class state%
    (super-new)
    (define/override (join state) this)
    (define/override (satisfy state) #f)
    (define/override (narrow [n #f]) '())
    (define/public (associate x v) this)
    (define/override (set-attribute attr) this)
    (define/override (add x) this)
    (define/override (add-constraint x) this)))

(define fail (new fail%))

;; t is a tree
(define (tree-associate t v state)
  (cond
   [(not (or (var? v) (tree? v) (pair? v) (null? v))) 
    fail]
   [(null? v)
    (for/fold ([state state]) ([node (tree-nodes t)])
      (send state associate node '()))]
   [else fail]))

(define succeed (new join%))

;; =============================================================================
;; operators

(define operator%
  (class object%
    (super-new)))

;; -----------------------------------------------------------------------------
;; conjunction

(define (conj . clauses)
  (for/fold ([state (new join%)]) ([base clauses])
    (send base join state)))

(define empty-state (new join%))

;; -----------------------------------------------------------------------------
;; disjunction

(define disj%
  (class* operator% (printable<%>)
    (init-field [states '()])
    (super-new)

    (define/public (custom-print p depth)
      (display (cons (object-name this%) states) p))
    (define/public (custom-write p)
      (write   (cons (object-name this%) states) p))
    (define/public (custom-display p) 
      (display (cons (object-name this%) states) p))

    (define/public (join state)
      (define result
        (for/list ([state^ states]) 
          (send state^ satisfy state)))
      (cond
       [(findf (curry eq? #t) result) state]
       [else
        (let ([clauses (filter identity result)])
          (cond
           [(null? clauses) #f]
           [(null? (cdr clauses)) (send (car clauses) join state)]
           [else (send state add-constraint (new this% [states clauses]))]))]))

    (define/public (satisfy state)
      (define result
        (for/list ([state^ states]) 
          (send state^ satisfy state)))
      (cond
       [(findf (curry eq? #t) result) #t]
       [else (apply disj (filter identity result))]))

    (define/public (augment-stream stream)
      (stream-interleave
       (stream-map (lambda (state) (send state augment-stream stream))
                   states)))

    (define/public (remove x)
      (new this% [states (remq x states)]))

    (define/public (add x)
      (new this% [states (cons x states)]))

    (define/public (update pair-or-attr state)
      (send 
       (send state remove this)
       add
       (apply disj (for/list ([thing states]) 
                     (send thing update pair-or-attr #f)))))))

(define (disj . clauses)
  (cond
   [(null? clauses) 
    (new fail%)]
   [(null? (cdr clauses)) 
    (send (car clauses) join (new join%))]
   [else
    (define satisfy-states
      (filter identity
              (for/list ([thing clauses])
                (send thing satisfy (new satisfy%)))))
    (cond
     [(findf (curryr eq? #t) satisfy-states) (new join%)]
     [else (new disj% [states satisfy-states])])]))

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

(define (dom->list d)
  (cond
   [(null-dom? d) '()]
   [else (cons (car-dom d) (dom->list (cdr-dom d)))]))

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
         [(null-dom? x) fail]
         [(value-dom? x)
          (cond
           [(memv-dom? x d) state]
           [else fail])]
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

    (define/public (merge attr^ state)
      (define new-d (intersection-dom d (send attr^ get-value)))
      (send (new dom% [rands (list x new-d)]) join state))

    (define/augment (augment-stream stream)
      (send (apply disj (for/list ([i (dom->list d)]) (== x i)))
            augment-stream stream))))

(define (dom/a x d)
  (new dom% [rands (list x d)]))

(define (+/o . n*)
  (new +% [rands n*]))

(define functionable% (interface () ->out ->rel))

(define +%
  (class* constraint% (functionable%)
    (super-new)
    (inherit-field [n* rands])

    (define/augment (join state)
      (cond
       [(or (null? n*) (null? (cdr n*))) 
        state]
       [(null? (cddr n*))
        (send state associate (car n*) (cadr n*))]
       [(null? (cdddr n*))
        (apply join/3 state n*)]
       [else
        (match-define (list n1 n2 rest ...) n*)
        (let ([n^ (var (gensym 'n))])
          (send (conj (+/o n1 n2 n^)
                      (apply +/o (cons n^ rest)))
                join state))]))

    (define (join/3 state u v w)
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
                (let* ([state            (send state add-constraint (+/o u v w))]
                       [state (and state (send (dom/a u new-u-dom) join state))]
                       [state (and state (send (dom/a v new-v-dom) join state))]
                       [state (and state (send (dom/a w new-w-dom) join state))])
                  state)]
               [else state]))))))

    ;; (+/o n*) = out
    (define/public (->out state k bad)
      (let ([n* (send state walk n*)])
        (cond
         [(andmap number? n*) (apply + n*)]
         [else 
          (define-values (m* x*) (partition number? n*))
          (new this% [rands (cons (apply + m*) x*)])])))

    (define/public (->rel n^ state)
      (let ([n* (send state walk n*)])
        (send (apply +/o (append n* (list n^))) join state)))

    (define/public (relevant-association? pair)
      (ormap (lambda (v) (memq v (map car pair))) n*))

    (define/public (relevant-attribute? attr)
      (ormap (lambda (v) (send attr same-as? dom% v)) n*))))

(define tree%
  (class unary-attribute%
    (super-new)

    (inherit-field rands)

    (define/augride (join state)
      (let* ([t (send state walk (car rands))])
        (cond
         [(list? t) 
          (send (new list% [rands (list t)]) join state)]
         [(send state has-attribute list% t) state]
         [(tree? t)
          (match-define (tree nodes) t)
          (and (list? nodes)
               (for/fold ([state state]) ([node nodes])
                 #:break (not state)
                 (send (list/a node) join state)))]
         [(var? t)
          (send state set-attribute (new this% [rands rands]))]
         [else fail])))

    (define/augride (satisfy state)
      (let ([t (send state walk (car rands))])
        (or (tree? t) (list? t) (tree/a t))))))

(define (tree/a t)
  (new tree% [rands (list t)]))

(define list%
  (class tree%
    (super-new)

    (init-field [partial #f])

    (inherit-field rands)
    (define ls (car rands))

    (define/override (update-rands rands)
      (new this% [rands rands] [partial partial]))

    (define/public (body ls)
      (disj (== ls `())
            (list/a (@ (cdr/o ls)))))
    
    (define/override (join state)
      (match (send (or partial (body ls)) satisfy state)
        [#f (new fail%)]
        [#t state]
        [c^ (send state set-attribute (new this% [rands rands] [partial c^]))]))

    (define/override (satisfy state)
      (match (send (or partial (body ls)) satisfy state)
        [#f #f]
        [#t #t]
        [c^ (new this% [rands rands] [partial c^])]))))

(define (list/a ls)
  (new list% [rands (list ls)]))

(define dots%
  (class list%
    (super-new)

    (init-field fn)
    (inherit-field partial rands)

    (define ls (car rands))

    (define/override (custom-print p depth)
      (display (cons (object-name this%) (list rands partial)) p))
    (define/override (custom-write p)
      (write   (cons (object-name this%) (list rands partial)) p))
    (define/override (custom-display p) 
      (display (cons (object-name this%) (list rands partial)) p))

    (define/override (update-rands rands)
      (new this% [rands rands] [partial partial] [fn fn]))

    (define/override (body ls)
      (disj (== ls `()) (conj (fn (@ (car/o ls))) (dots/a fn (@ (cdr/o ls))))))

    (define/override (join state)
      (match (send (or partial (body ls)) satisfy state)
        [#f (new fail%)]
        [#t state]
        [c^
         (cond
          [(is-a? c^ join%) (send c^ join state)]
          [else (send state set-attribute
                      (new this% [rands rands] [partial c^] [fn fn]))])]))

    (define/override (satisfy state)
      (match (send (or partial (body ls)) satisfy state)
        [#f #f]
        [#t #t]
        [c^ (new this% [rands rands] [partial c^] [fn fn])]))))

(define (dots/a fn ls)
  (new dots% [fn fn] [rands (list ls)]))

(define size%
  (class binary-attribute%
    (super-new)

    (inherit-field rands)
    (define x (car rands))

    (define/augment (join state)
      (match (send (body (send state walk x) (get-value)) satisfy state)
        [#f #f]
        [#t state]
        [c^ (send state set-attribute (new this% [rands rands] [body c^]))]))

    (define/augment (satisfy state)
      (match (send (body (send state walk x) (get-value)) satisfy state)
        [#f #f]
        [#t #t]
        [c^ (new this% [rands rands] [body c^])]))

    ;; x is a Tree, n is a (Number U Domain)
    ;; size of everything in x sums up to n
    (define (body x n)
      ;; n* is a list of Numbers, one for each node of x
      (error 'hi "here")
      #;
      (disj
       (conj (! (tree/a x))
             (associate n 1))
       (conj (list/a x)
             (length/a x n))
       (conj (tree/a x) 
             (! (list/a x))
             (let ([n* (var 'n*)])
               (conj 
                (map/o (lambda (node n) (size/a node n)) (nodes/o x) n*)
                (apply/o +fd (append/o n* (list n))))))))

    (define/public (get-value)
      (cond
       [(null? (cdr rands))
        (if (list? x) (length x) (range-dom 0 100))]
       [else (cadr rands)]))))

(define (size/a x n)
  (new size% [rands (list x n)]))

(define length%
  (class binary-attribute%
    (super-new)
    (inherit-field rands)
    (define x (car rands))

    (define/augment (join state)
      (cond
       [(send state get-attribute this% x)
        => (lambda (n) (send state associate (cadr rands) n))]
       [(send (tree/a x) join state)
        => (lambda (state)
             (let ([x (send state walk x)]
                   [n (send state walk (cadr rands))])
               (cond
                [(and (list? x) (number? n))
                 (and (= (length x) n) state)]
                [(list? x)
                 (send state associate (length x) n)]
                [(tree? x)
                 (match-define (tree nodes) x)
                 (define n* (for/list ([node nodes]) (var (gensym'n))))
                 (send (conj (apply conj (for/list ([node nodes] [n n*])
                                           (length/a node n)))
                             (apply +/o (append n* (list n))))
                       join state)]
                [(number? n)
                 (send state associate (for/list ([i n]) (var 'i)) x)]
                [else (send state set-attribute (new this% [rands (list x n)]))])))]
       [else #f]))

    (define/public (get-value)
      (cond
       [(null? (cdr rands))
        (if (list? x) (length x) (range-dom 0 100))]
       [else (cadr rands)]))))

(define (length/a ls n) (new length% [rands (list ls n)]))

(define (run state [n #f])
  (cond
   [(send state join (new join%))
    => (lambda (state) (send state narrow n))]
   [else '()]))

(define cdr%
  (class* constraint% (functionable%)
    (super-new)
    (inherit-field rands)

    (define ls (car rands))

    (define/public (->out state k bad)
      (let ([ls (send state walk ls)])
        (cond
         [(pair? ls) (cdr ls)]
         [(object? ls)
          (let ([ls (send ls ->out state k bad)])
            (cond
             [(pair? ls) (cdr ls)]
             [(not (or (var? ls) (object? ls))) (k bad)]
             [else (new cdr% [rands (list ls)])]))]
         [(not (var? ls)) (k bad)]
         [else (new cdr% [rands (list ls)])])))

    (define/public (->rel v state)
      (let ([ls (send state walk ls)])
        (cond
         [(is-a? ls delay%)
          (let ([lso (var 'lso)])
            (let ([state (send ls ->rel lso state)])
              (and state (send (cdr/o lso v) join state))))]
         [else (send (cdr/o ls v) join state)])))

    (define/augment (join state)
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) 
          (send state associate (cdr ls) out)]
         [else (send state associate (cons (var 'a) out) ls)])))

    (define/augment (augment-stream stream)
      (cond
       [(null? (cdr rands))
        (stream-map (lambda (state)
                      (and state
                           (let ([ls (send state walk (car rands))])
                             (cond
                              [(pair? ls) state]
                              [else (send state associate (cons (var 'a) (var 'd)) ls)]))))
                    stream)]
       [else (error 'augment-stream "not sure why this would happen")]))))

(define (cdr/o . rands)
  (new cdr% [rands rands]))

(define car%
  (class* constraint% (functionable%)
    (super-new)
    (inherit-field rands)

    (define ls (car rands))

    (define/public (->out state k bad)
      (let ([ls (send state walk ls)])
        (cond
         [(pair? ls) (car ls)]
         [(object? ls)
          (let ([ls (send ls ->out state k bad)])
            (cond
             [(pair? ls) (car ls)]
             [(not (or (var? ls) (object? ls))) (k bad)]
             [else (new car% [rands (list ls)])]))]
         [(not (var? ls)) (k bad)]
         [else (new car% [rands (list ls)])])))

    (define/public (->rel v state)
      (let ([ls (send state walk ls)])
        (cond
         [(is-a? ls delay%)
          (let ([lso (var 'lso)])
            (let ([state (send ls ->rel lso state)])
              (and state (send (car/o lso v) join state))))]
         [else (send (car/o ls v) join state)])))

    (define/augment (join state)
      (unless (not (null? (cdr rands)))
        (error 'join "join without ->rel: ~a ~a\n" this state))
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) 
          (send state associate (car ls) out)]
         [else (send state associate (cons out (var 'd)) ls)])))

    (define/augment (augment-stream stream)
      (cond
       [(null? (cdr rands))
        (stream-map (lambda (state)
                      (and state
                           (let ([ls (send state walk (car rands))])
                             (cond
                              [(pair? ls) state]
                              [else (send state associate (cons (var 'a) (var 'd)) ls)]))))
                    stream)]
       [else (error 'augment-stream "not sure why this would happen")]))))

(define (car/o . rands)
  (new car% [rands rands]))

(define sub1%
  (class* constraint% (functionable%)
    (super-new)

    (inherit-field rands)
    (define n (car rands))

    (define/public (->rel v state)
      (let ([n (send state walk n)])
        (cond
         [(object? n)
          (let ([n^ (var 'n^)])
            (let ([state (send n ->rel n^ state)])
              (and state (send (+/o v 1 n^) join state))))]
         [else (send (+/o v 1 n) join state)])))

    (define/public (->out state k bad)
      (let ([n (send state walk n)])
        (cond
         [(object? n) 
          (let ([n (send n ->out state k bad)])
            (cond
             [(object? n) (new this% [rands (list n)])]
             [(number? n) (sub1 n)]
             [(var? n) (new this% [rands (list n)])]
             [else (k bad)]))]
         [(number? n) (sub1 n)]
         [(var? n) (new this% [rands (list n)])]
         [else (k bad)])))))

(define sub1/o
  (case-lambda
   [(n) (new sub1% [rands (list n)])]
   [(n m) (+/o n 1 m)]))

(define delay%
  (class* object% (functionable% printable<%>)
    (super-new)

    (init-field c)

    (define/public (custom-print p depth)
      (display (list '@ c) p))
    (define/public (custom-write p)
      (write   (list '@ c) p))
    (define/public (custom-display p) 
      (display (list '@ c) p))

    (unless (is-a? c functionable%)
      (error 'delay% "given non-functionable% ~a" c))

    (define/public (->rel v state)
      (send c ->rel v state))

    (define/public (->out state k bad)
      (let ([ans (send c ->out state k bad)])
        (cond
         [(object? ans) (new this% [c ans])]
         [else ans])))

    (define/public (augment-stream stream)
      (send c augment-stream stream))))

(define (@ c) (new delay% [c c]))

;; (mapo rel ls ... out)
(define map%
  (class constraint%
    (init-field rel ls* out)
    (super-new [rands (list rel ls* out)])
    
    (define/augment (join state)
      (let ([ls* (send state walk ls*)]
            [out (send state walk out)])
        (cond
         [(andmap pair? ls*)
          ;; ((a . d) ...) (o . r)
          (cond
           [(pair? out)
            (send (conj (apply rel (append (map car ls*) (list (car out))))
                        (new this% [rel rel] [ls* (map cdr ls*)] [out (cdr out)]))
                  join state)]
           [else
            (let ([o (var 'o)] [d (var 'r)])
              (send (conj (== (cons o d) out)
                          (apply rel (append (map car ls*) (o)))
                          (new this% [rel rel] [ls* (map cdr ls*)] [out d]))
                    join state))])]
         [(ormap null? ls*)
          ;; (l ... () s ...) (o ...)
          (send (conj (apply conj (map (lambda (x) (== x '())) ls*))
                      (== out '()))
                join state)]
         [(pair? out)
          (error 'here "here")]
         [else (send state add-constraint (new this% [rel rel] [ls* ls*] [out out]))])))))

(define (map/o rel . ls*o)
  (let ([rev-ls*o (reverse ls*o)])
    (new map% [rel rel] [ls* (reverse (cdr rev-ls*o))] [out (car rev-ls*o)])))

