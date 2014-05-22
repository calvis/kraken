#lang racket/base

;; todo: struct@
(require racket/trace)

(provide (all-defined-out)
         (all-from-out "variables.rkt"))
(require (for-syntax racket/base) 
         (for-syntax syntax/parse))

(require "variables.rkt")

(struct -eigen cvar ())
(define (eigen x) (-eigen "e" x))
(define eigen? -eigen?)

(require (rename-in racket/stream [stream-append stream-append-proc]))

(define-syntax-rule (ignore e ...) (void))

(define-syntax-rule (display/return expr)
  (let ([result expr]) (display " return:\n") (pretty-print result) expr))

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
  (if (is-a? o functionable<%>) (send o ->out state k bad) o))

(define-syntax-rule (case-shape x [t clause] ...)
  (disj (==> (shape x `t) clause) ...))

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
            (cons 'tree 
                  (for/fold ([nodes '()]) ([node (tree-nodes x)])
                    (cond
                     [(list? node) (append nodes node)]
                     [else (append nodes (list '@ node))])))
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

    (init-field [rator this%] [rands '()] [scope '()])

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
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code rands)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    rands (range 0 (length rands)))))

    (define/public (update-rands rands)
      (new this% [rands rands] [scope scope]))

    (define/pubment (join state)
      (call/cc
       (lambda (k)
         (cond
          [(findf (curryr is-a? functionable<%>) rands)
           (define-values (new-state new-rands)
             (for/fold ([state state] [rands '()]) ([r rands])
               (cond
                [(is-a? r functionable<%>)
                 (let ([out (var 'out)])
                   (values (send r ->rel out state)
                           (cons out rands)))]
                [else (values state (cons r rands))])))
           (send (send this update-rands (reverse new-rands)) join new-state)]
          [else (inner state join state)]))))

    (define/pubment (satisfy state)
      (call/cc
       (lambda (k)
         (let ([rands^ (map (update-constraints state k #f) rands)])
           (cond
            [(equal? rands rands^)
             (inner #f satisfy state)]
            [else 
             (send (send this update-rands rands^) satisfy state)])))))

    (define/public (add-scope ls)
      (new this% [rands rands] [scope (cons ls scope)]))

    (define (force-delays stream)
      (let ([rands (filter (curryr is-a? functionable<%>) rands)])
        (for/fold ([stream stream]) ([r rands])
          (send r augment-stream stream))))

    ;; State Stream -> Stream
    (define/pubment (augment-stream stream)
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
;; associate

(define (== x v)
  (new ==% [rands (list x v)]))

(define (≡ x v) (== x v))

(define ==%
  (class constraint%
    (super-new)
    (inherit-field rands scope)
    (match-define (list x v) rands)

    (define/augment (join state)
      (send state associate x v scope))

    ;; problem: state isn't always a satisfy state.
    (define/augment (satisfy state)
      (match (send (new satisfy%) associate x v) 
        [#t #t]
        [#f #f]
        [state^ (send state^ satisfy state)]))))

;; =============================================================================
;; states

(define state%
  (class* object% (equal<%> printable<%>)
    (super-new)

    (init-field [s '()] [c '()] [a '()])

    (unless (andmap (lambda (c) (not (is-a? c join%))) c)
      (error 'state% "invalid stuffs:\n ~a\n ~a" this c))

    (define/public (equal-to? obj recur?)
      (and (recur? s (get-field s obj))
           (recur? c (get-field c obj))
           (recur? a (get-field a obj))))

    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code s) (hash-code c) (hash-code a)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (+ (* 1 (hash-code s))
         (* 10 (hash-code c))
         (* 100 (hash-code a))))

    (define/public (add-scope ls)
      (for/fold ([state (new this% [s s])]) ([thing (append c a)])
        (send state add (send thing add-scope ls))))

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
        (cond 
         [(satisfy-p (car p) (cdr p)) => (curryr append s)]
         [else #f])))

    ;; Association -> [List-of Association]
    (define (satisfy-p x v)
      (let ([x (walk x)] [v (walk v)])
        (cond
         [(eq? x v) (list)]
         [(var? x) (list (cons x v))]
         [(var? v) (list (cons v x))]
         [(and (pair? x) (pair? v))
          (let ([a (satisfy-p (car x) (car v))])
            (and a (let ([d (satisfy-p (cdr x) (cdr v))])
                     (and d (append a d)))))]
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
       [(is-a? x attribute%)
        (set-attribute x)]
       [(is-a? x operator%)
        (add-constraint x)]
       [(and (is-a? x join%)
             (is-a? this pre-join%))
        (for/fold ([state this]) ([thing (append (get-field c x)
                                                 (get-field a x))])
          (send state add thing))]
       [(is-a? x state%)
        (join x)]
       [else (error 'add "cannot add ~a to ~a" x this)]))

    (define/public (add-constraint c^)
      (new this% [s s] [c (cons c^ c)] [a a]))

    (define/public (join state)
      (cond
       [(and (is-a? state pre-join%))
        (join (send state join (new join%)))]
       [else (send+ state (join-s s) (join-c a) (join-c c))]))

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
      (define answer-stream
        (send this augment-stream (list (new join%))))
      (take (stream-filter (compose not (curryr is-a? fail%)) answer-stream) n))

    (define/public (reify v)
      (let ([v (walk v)])
        (walk/internal v (reify-s v '()))))))

;; check-scope : 
;;   [List-of EigenVar] [List-of CVar] [List-of [List-of CVar]] -> Boolean
;; returns #t if scope is correctly observed, and #f otherwise
;; examples: 
;;    ()  (x) ((x) (e) (y)) = #t
;;    (e) (x) ((x) (e) (y)) = #f
;;    (e) (y) ((x) (e) (y)) = #t
(define (check-scope? e* x* scope)
  (or (null? e*)
      (null? scope)
      (and (not (ormap (lambda (x) (memq x x*)) (car scope)))
           (check-scope?
            (for/fold ([e* e*]) ([e (car scope)]) (remq e e*))
            (for/fold ([x* x*]) ([x (car scope)]) (remq x x*))
            (cdr scope)))))

(require (except-in rackunit fail))
(let ([e (eigen 'e)] [x (var 'x)] [y (var 'y)])
  (let ([scope (list (list x) (list e) (list y))])
    (check-true  (check-scope? (list)   (list x) scope))
    (check-false (check-scope? (list e) (list x) scope))
    (check-true  (check-scope? (list e) (list y) scope))))

(require racket/set)
;; [List-of CVar] Subsitution -> [List-of CVar]
(define (related-to x* s)
  ;; [Set-of CVar]
  ;; variables we want to find the related variables to
  (define X (list->seteq x*))

  ;; [List-of [Set-of CVar]]
  ;; sets of all related variables based on unifications in s
  (define related (map (compose list->seteq (lambda (x) (filter* cvar? x))) s))

  ;; [Set-of Variable] [List-of [Set-of Variable] -> [Set-of Variable]
  ;; computes all variables that are related to variables in X
  (define (loop X related)
    (cond
     [(null? related) X]
     [else 
      (define-values (r not-r)
        (partition (lambda (S) (not (set-empty? (set-intersect X S)))) related))
      (cond
       [(null? r) X]
       [else (loop (apply set-union X r) not-r)])]))

  ;; returns the total set of related variables at the end
  (set->list (loop X related)))

(define join%
  (class state%
    (super-new)
    (inherit walk)
    (inherit-field s c a)

    (define/public (associate x v [scope '()])
      (let ([x (walk x)] [v (walk v)])
        (let ([state (unify x v)])
          ;; x is a var or an eigen
          ;; v could have vars and eigens in it
          (define-values (e* x*)
            (partition eigen? (related-to (filter* cvar? (cons x v)) s)))
          (cond
           [(check-scope? e* x* scope) state]
           [else (new fail%)]))))

    (define/public (unify x v)
      (cond
       [(eq? x v) this]
       [(and (is-a? x functionable<%>) (not (object? v)))
        (send x ->rel v this)]
       [(and (is-a? v functionable<%>) (not (object? x)))
        (send v ->rel x this)]
       [(var? x) 
        (send (new this% [s (cons (cons x v) s)] [c c] [a a])
              update (cons x v))]
       [(var? v)
        (send (new this% [s (cons (cons v x) s)] [c c] [a a])
              update (cons v x))]
       [(and (pair? x) (pair? v))
        (send (unify (car x) (car v)) unify (cdr x) (cdr v))]
       [(tree? x)
        (tree-associate x v this)]
       [(tree? v)
        (tree-associate v x this)]
       [(equal? x v) this]
       [else (new fail% [trace this])]))

    (define/public (augment-stream stream)
      (stream-filter
       (compose not (curryr is-a? fail%))
       (let ([stream (stream-map (lambda (state) (send state join-s s)) stream)])
         (for/fold ([stream stream]) ([thing (append c a)])
           (send thing augment-stream stream)))))

    (define/public (update pair)
      (send (send (new this% [s s]) join-a a) join-c c))))

(define pre-join%
  (class join% 
    (super-new)
    (inherit-field s c a)

    (define/override (join-c c^)
      (unless (or (null? c) (null? (cdr c)))
        (error 'join-c "prejoin ~a can't join with ~a" this c^))
      (send (new join% [s s] [c c] [a a]) join-c c^))

    (define/override (join-a a^)
      (unless (or (null? a) (null? (cdr a)))
        (error 'join-a "prejoin ~a can't join with ~a" this a^))
      (send (new join% [s s] [c c] [a a^]) join-a a^))))

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
                      [#t state^] [#f #f] [state^^ state^^])])]
         [(equal? x v) #t]
         [else #f])))

    (define/public (augment-stream stream)
      (send (new join% [s s] [c c] [a a]) augment-stream stream))))

(define fail%
  (class* state% (printable<%>)
    (super-new)
    (init-field [trace #f])

    (define/override (custom-print p depth)
      (display (list 'fail% trace) p))
    (define/override (custom-write p)
      (write   (list 'fail% trace) p))
    (define/override (custom-display p) 
      (display (list 'fail% trace) p))

    (define/override (join state) this)
    (define/override (satisfy state) #f)
    (define/override (narrow [n #f]) '())
    (define/public (associate x v) this)
    (define/public (unify x v) this)
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
;; existentials

(provide exists fresh)

(define-syntax-rule (exists (x ...) bodys ... body)
  (let ([x (var (gensym 'x))] ...)
    (unless (void? bodys)
      (error 'exists "not void\n expression: ~a" 'bodys))
    ... 
    (send body add-scope (list x ...))))

(define-syntax-rule (fresh (x ...) body ...)
  (exists (x ...) body ...))

;; =============================================================================
;; universals

(provide forall)

(define-syntax-rule (forall (x ...) bodys ... body)
  (let ([x (eigen (gensym 'x))] ...) 
    (unless (void? bodys)
      (error 'forall "intermediate expression was not void\n ~a" 'bodys))
    ... 
    (send body add-scope (list x ...))))

;; =============================================================================
;; operators

(define operator%
  (class object%
    (super-new)))

;; -----------------------------------------------------------------------------
;; conjunction

(define (conj . clauses)
  (for/fold ([state (new pre-join%)]) ([base (reverse clauses)])
    (send state add base)))

(define empty-state (new join%))

;; -----------------------------------------------------------------------------
;; disjunction

(define disj%
  (class* operator% (printable<%>)
    (init-field [states '()] [failures '()])
    (super-new)

    (define/public (custom-print p depth)
      (display (cons (object-name this%) states) p))
    (define/public (custom-write p)
      (write   (cons (object-name this%) states) p))
    (define/public (custom-display p) 
      (display (cons (object-name this%) states) p))

    (unless (> (length states) 1)
      (error 'disj% "invalid states: ~a" states))

    (define/public (join state)
      (define result
        (filter identity (for/list ([state^ states])
                           (send state^ satisfy state))))
      (cond
       [(findf (curry eq? #t) result) state]
       [(null? result) (new fail% [trace this])]
       [(null? (cdr result)) (send (car result) join state)]
       [else (send state add-constraint (new this% [states result]))]))

    (define/public (satisfy state)
      (define result 
        (filter identity 
                (for/list ([state^ states]) 
                  (send state^ satisfy state))))
      (cond
       [(findf (curry eq? #t) result) #t]
       [(null? result) #f]
       [(null? (cdr result)) (car result)]
       [else (new disj% [states result])]))

    (define/public (augment-stream stream)
      (stream-interleave
       (stream-map (lambda (state) (send state augment-stream stream))
                   states)))

    (define/public (remove x)
      (new this% [states (remq x states)]))

    (define/public (add x)
      (new this% [states (cons x states)]))))

(define (disj . clauses)
  (cond
   [(null? clauses) 
    (new fail%)]
   [(null? (cdr clauses)) 
    (send (car clauses) join (new join%))]
   [else (new disj% [states clauses])]))

;; =============================================================================
;; examples

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
        (or (not (not (memv-dom? x d)))
            (cond
             [(send state get-attribute this% x)
              => (lambda (attr^)
                   (let ([i (intersection-dom attr^ d)])
                     (or (equal? i attr^) this)))]
             [else this]))))

    (define/public (merge attr^ state)
      (define new-d (intersection-dom d (send attr^ get-value)))
      (send (new dom% [rands (list x new-d)]) join state))

    (define/augment (augment-stream stream)
      (send (apply disj (for/list ([i (dom->list d)]) (== x i)))
            augment-stream stream))))

(define (dom/a x d)
  (new dom% [rands (list x d)]))

(define (+@ . n*)
  (new +% [rands n*]))

(define functionable<%> (interface () ->out ->rel))

(define +%
  (class* constraint% (functionable<%>)
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
        (send
         (exists (n^)
           (conj (+@ n1 n2 n^)
                 (apply +@ (cons n^ rest))))
         join state)]))

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
                (let* ([state            (send state add-constraint (+@ u v w))]
                       [state (and state (send (dom/a u new-u-dom) join state))]
                       [state (and state (send (dom/a v new-v-dom) join state))]
                       [state (and state (send (dom/a w new-w-dom) join state))])
                  state)]
               [else state]))))))

    ;; (+@ n*) = out
    (define/public (->out state k bad)
      (let ([n* (send state walk n*)])
        (cond
         [(andmap number? n*) (apply + n*)]
         [else 
          (define-values (m* x*) (partition number? n*))
          (new this% [rands (cons (apply + m*) x*)])])))

    (define/public (->rel n^ state)
      (let ([n* (send state walk n*)])
        (send (apply +@ (append n* (list n^))) join state)))

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
                 (send (tree/a node) join state)))]
         [(var? t)
          (send state set-attribute (new this% [rands rands]))]
         [else fail])))

    (define/augride (satisfy state)
      (let ([t (send state walk (car rands))])
        (or (tree? t) (list? t) (tree/a t))))))

(define (tree/a t)
  (new tree% [rands (list t)]))

(define list%
  (class* tree% (printable<%>)
    (super-new)

    (init-field [partial #f])

    (inherit-field rands)
    (define ls (car rands))

    (define/override (custom-print p depth)
      (display (list (object-name this%) rands partial) p))
    (define/override (custom-write p)
      (write   (list (object-name this%) rands partial) p))
    (define/override (custom-display p)
      (display (list (object-name this%) rands partial) p))

    (define/override (update-rands rands)
      (new this% [rands rands] [partial partial]))

    (define/public (body ls)
      (disj (== ls `())
            (exists (a d)
              (==> (shape ls (cons (any) (any)))
                (list/a (cdr@ ls))))))
    
    (define/override (join state)
      (match (send (or partial (body ls)) satisfy state)
        [#f (new fail% [trace this])]
        [#t state]
        [c^ (send state set-attribute (new this% [rands rands] [partial c^]))]))

    (define/override (satisfy state)
      (match (send (or partial (body ls)) satisfy state)
        [#f #f]
        [#t #t]
        [c^ (new this% [rands rands] [partial c^])]))))

(define (list/a ls)
  (new list% [rands (list ls)]))

(define ==>%
  (class* operator% (printable<%>)
    (super-new)
    (init-field test consequent [scope '()])

    (define/public (custom-print p depth)
      (display (list (object-name this%) test consequent) p))
    (define/public (custom-write p)
      (write   (list (object-name this%) test consequent) p))
    (define/public (custom-display p) 
      (display (list (object-name this%) test consequent) p))

    (define/public (join state)
      (match (send test satisfy state)
        [#t (send consequent join state)]
        [#f (new fail% [trace this])]
        [test^ (send state add (==> test^ consequent))]))

    (define/public (satisfy state)
      (match (send test satisfy state)
        [#t (send consequent satisfy state)]
        [#f #f]
        [test^ (==> test^ consequent)]))

    (define/public (augment-stream stream)
      (error '==>% "trying to augment: ~a\n" this))

    (define/public (add-scope ls)
      (new this% [test test] [consequent consequent] [scope (cons ls scope)]))))

(define (==> t [c succeed]) 
  (new ==>% [test t] [consequent c]))

(define shape%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (match-define (list x t) rands)

    (define/augment (join state)
      (error 'join "shape% not joinable"))

    (define/augment (satisfy state)
      (let ([x (send state walk x)] [t (send state walk t)])
        (cond
         [(any? t) #t]
         [(and (pair? x) (pair? t))
          (send (conj (shape (car x) (car t))
                      (shape (cdr x) (cdr t)))
                satisfy state)]
         [(symbol? t)
          (send (== x t) satisfy state)]
         [(null? t)
          (send (== x `()) satisfy state)]
         [(and (not (var? x)) (pair? t)) #f]
         [else (shape x t)])))))

(define (shape x t) (new shape% [rands (list x t)]))

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
      (disj (==> (shape ls `()))
            (==> (shape ls (cons (any) (any)))
                 (conj (fn (car@ ls)) (dots/a fn (cdr@ ls))))))

    (define/override (join state)
      (match (send (or partial (body ls)) satisfy state)
        [#f (new fail% [trace this])]
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
                 (define n* (for/list ([node nodes]) (var 'n)))
                 (let ([state (send (apply +@ (append n* (list n))) join state)])
                   (send (apply conj (for/list ([node nodes] [n n*])
                                       (length/a node n)))
                         join state))]
                [(number? n)
                 (send state associate (for/list ([i n]) (var 'n)) x)]
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
  (class* constraint% (functionable<%>)
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
        (send (cdr@ ls v) join state)))

    (define/augment (join state)
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) 
          (send state associate (cdr ls) out)]
         [else 
          (exists (a)
            (send state associate (cons a out) ls))])))

    (define/augment (augment-stream stream)
      (cond
       [(null? (cdr rands))
        (stream-map (lambda (state)
                      (and state
                           (let ([ls (send state walk (car rands))])
                             (cond
                              [(pair? ls) state]
                              [else 
                               (exists (a d)
                                 (send state associate (cons a d) ls))]))))
                    stream)]
       [else (error 'augment-stream "not sure why this would happen")]))))

(define (cdr@ . rands)
  (new cdr% [rands rands]))

(define car%
  (class* constraint% (functionable<%>)
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
        (send (car@ ls v) join state)))

    (define/augment (join state)
      (unless (not (null? (cdr rands)))
        (error 'join "join without ->rel: ~a ~a\n" this state))
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) (send state associate (car ls) out)]
         [else 
          (exists (d)
            (send state associate (cons out d) ls))])))

    (define/augment (augment-stream stream)
      (cond
       [(null? (cdr rands))
        (stream-map (lambda (state)
                      (and state
                           (let ([ls (send state walk (car rands))])
                             (cond
                              [(pair? ls) state]
                              [else 
                               (exists (a d)
                                 (send state associate (cons a d) ls))]))))
                    stream)]
       [else (error 'augment-stream "not sure why this would happen")]))))

(define (car@ . rands)
  (new car% [rands rands]))

(define sub1%
  (class* constraint% (functionable<%>)
    (super-new)

    (inherit-field rands)
    (define n (car rands))

    (define/public (->rel v state)
      (let ([n (send state walk n)])
        (cond
         [(object? n)
          (exists (n^)
            (let ([state (send n ->rel n^ state)])
              (and state (send (+@ v 1 n^) join state))))]
         [else (send (+@ v 1 n) join state)])))

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

(define sub1@
  (case-lambda
   [(n) (new sub1% [rands (list n)])]
   [(n m) (+@ n 1 m)]))

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
            (exists (o d)
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

(define (map@ rel . ls*o)
  (let ([rev-ls*o (reverse ls*o)])
    (new map% [rel rel] [ls* (reverse (cdr rev-ls*o))] [out (car rev-ls*o)])))

(define (partial-mixin %)
  (class % 
    (super-new)
    (init-field [partial #f])
    (inherit-field rands)

    (define/augment (join state)
      (match (send (or partial (send this body . rands)) satisfy state)
        [#f (new fail%)]
        [#t state]
        [c^ (cond
             [(is-a? c^ join%) (send state join c^)]
             [else (send state add-constraint
                         (new this% [rands rands] [partial c^]))])]))
    
    (define/augment (satisfy state)
      (match (send (or partial (send this body . rands)) satisfy state)
        [#f #f]
        [#t #t]
        [c^ (new this% [rands rands] [partial c^])]))

    (define/augment (augment-stream stream)
      (send (or partial (send this body . rands)) augment-stream stream))))

(define-syntax (define-constraint stx)
  (syntax-parse stx
    [(define-constraint (name args ...) interp)
     #'(define (name args ...)
         (define name% 
           (class constraint% (super-new)
             (define/public (body args ...) interp)))
         (new (partial-mixin name%) [rands (list args ...)]))]))

(define (filter* f t)
  (cond
   [(f t) (list t)]
   [(pair? t) (append (filter* f (car t)) (filter* f (cdr t)))]
   [else (list)]))
