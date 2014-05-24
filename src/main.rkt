#lang racket/base

(require (for-syntax racket/base syntax/parse))
(require (rename-in racket/stream [stream-append stream-append-proc]))
(require racket/class 
         (except-in racket/match ==)
         racket/list
         racket/function
         racket/pretty)

(require "data.rkt")

(provide (all-from-out "data.rkt")
         (all-defined-out))

(define-syntax-rule (stream-append s* ... s)
  (let ([last (lambda () s)]
        [pre (stream-append-proc s* ...)])
    (define (loop stream)
      (cond
       [(stream-empty? stream) (last)]
       [else (stream-cons (stream-first stream)
                          (loop (stream-rest stream)))]))
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

(define ((update-functionable state k) r)
  (if (is-a? r functionable<%>) (send r ->out state k) r))

(define-syntax-rule (case-shape x [t clause] ...)
  (disj (==> (shape x `t) clause) ...))

;; =============================================================================
;; reification

(define (extend-rs v s)
  `((,v . ,(reify-n v (size-s s))) . ,s))

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
;; constraints and attributes

(define streamable<%> (interface () augment-stream))
(define functionable<%> (interface () ->rel))

(define base%
  (class* object% (printable<%> streamable<%>)
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

    (define/public (update-rands rands)
      (new this% [rands rands] [scope scope]))

    (define/public (run state)
      (send (send this update state) combine state))

    (define/pubment (update state)
      (call/cc
       (lambda (k)
         (let ([rands^ (map (update-functionable state k) rands)])
           (cond
            [(findf (curryr is-a? functionable<%>) rands^)
             (update-rands rands^)]
            [(andmap eq? rands rands^)
             (inner this update state)]
            [else (send (update-rands rands^) update state)])))))

    (define/public (add-scope ls)
      (new this% [rands rands] [scope (cons ls scope)]))

    ;; State Stream -> Stream
    (define/public (augment-stream stream)
      (stream-filter
       (compose not (curryr is-a? fail%))
       (stream-map 
        (lambda (state)
          (call/cc 
           (lambda (k)
             (let ([rands (map (update-functionable state k) rands)])
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
                 (send (send this update-rands (reverse new-rands))
                       run new-state)]
                [else (send this run state)])))))
        stream)))

    (define/public (combine state)
      (send state set-stored this))))

(define constraint% 
  (class* base% (equal<%>)
    (super-new)
    (inherit-field rands)

    (define/public (equal-to? obj recur?)
      (and (= (length rands) (length (get-field rands obj)))
           (andmap recur? rands (get-field rands obj))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code rands)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    rands (range 0 (length rands)))))))

(define attribute%
  (class* base% (equal<%>)
    (super-new)
    (inherit-field rands)

    (define/public (equal-to? obj recur?)
      (and (or (implementation? 
                (send obj get-rator)
                (class->interface this%))
               (implementation? 
                this%
                (class->interface (send obj get-rator))))
           (eq? (car rands) (car (get-field rands obj)))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code rands)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    rands (range 0 (length rands)))))

    (define/override (combine state)
      (cond
       [(send state has-stored this)
        => (lambda (this^)
             ;; we have two identical attributes on the same variable,
             ;; see if they need to merge and take appropriate actions
             (send this merge this^ (send state remove-stored this^)))]
       [else (send state set-stored this)]))))

(define unary-attribute%
  (class attribute% 
    (super-new)

    (define/public (merge a state)
      (cond
       [(implementation? (send a get-rator) (class->interface this%))
        (send state set-stored a)]
       [else (send state set-stored this)]))))

(define binary-attribute%
  (class attribute% 
    (super-new)))

;; =============================================================================
;; operators

(define operator%
  (class object%
    (super-new)))

;; -----------------------------------------------------------------------------
;; associate

(define (≡ x v) (== x v))

(define (== x v)
  (new ==% [x x] [v v]))

(define ==%
  (class* operator% (printable<%>)
    (init-field x v [scope '()])
    (super-new)

    (define/public (custom-print p depth)
      (display (list (object-name this%) x v) p))
    (define/public (custom-write p)
      (write   (list (object-name this%) x v) p))
    (define/public (custom-display p) 
      (display (list (object-name this%) x v) p))
    
    (define/public (update state)
      (let ([x (send state walk x)]
            [v (send state walk v)])
        (send (new state%) associate x v scope)))

    (define/public (combine state)
      (send state associate x v scope))

    (define/public (run state)
      (send state associate x v scope))

    (define/public (add-scope ls)
      (new this% [x x] [v v] [scope (cons ls scope)]))))

;; =============================================================================
;; states

(define state%
  (class* object% (equal<%> printable<%>)
    (super-new)

    (init-field [subst '()] [store '()])

    (define (idemize subst)
      (map (lambda (p) (list (car p) (walk/internal (cdr p) subst)))
           subst))

    (define sexp-me
      (list (object-name this%) (idemize subst) store))
    
    (define/public (custom-print p depth)
      (display sexp-me p))
    (define/public (custom-write p)
      (write sexp-me p))
    (define/public (custom-display p) 
      (display sexp-me p))

    (unless (list? subst)
      (error 'state% "subst is not a list\n subst: ~a" subst))

    (unless (list? store)
      (error 'state% "store is not a list\n store: ~a" store))

    (define/public (equal-to? obj recur?)
      (and (is-a? obj this%)
           (recur? (idemize subst) (idemize (get-field subst obj)))
           (recur? store (get-field store obj))))

    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code subst) (hash-code store)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (+ (hash-code subst) (* 10 (hash-code store))))

    (define/public (add-scope ls)
      (for/fold
        ([state (add-subst (new this%))])
        ([thing store])
        (send state set-stored (send thing add-scope ls))))

    (define/public (walk u)
      (walk/internal u subst))

    (define/public (remove-stored thing)
      (new this% [subst subst] [store (remove thing store)]))

    (define/public (has-stored thing)
      (findf (curry equal? thing) store))

    (define/public (get-stored x% x)
      (cond
       [(findf (curry equal? (new x% [rands (list x)])) store)
        => (lambda (thing2) (send thing2 get-value))]
       [else #f]))

    (define/public (set-stored thing)
      (new this% [subst subst] [store (cons thing store)]))

    (define/public (narrow [n #f])
      (define (take stream n)
        (cond
         [(and n (zero? n)) '()]
         [(stream-empty? stream) '()]
         [else (cons (stream-first stream) 
                     (take (stream-rest stream) (and n (sub1 n))))]))
      (define answer-stream
        (send this augment-stream (list (new state%))))
      (take (stream-filter (compose not (curryr is-a? fail%)) answer-stream) n))

    (define/public (reify v)
      (let ([v (walk v)])
        (walk/internal v (reify-s v '()))))

    (define/public (associate x v [scope '()])
      (let ([x (walk x)] [v (walk v)])
        (let ([state (unify x v)])
          (define-values (e* x*)
            (partition eigen? (related-to 
                               (filter* cvar? (cons x v)) subst)))
          (cond
           [(check-scope? e* x* scope) state]
           [else (new fail% [trace `(eigen ,x ,v)])]))))

    (define/public (unify x v)
      (cond
       [(eq? x v) this]
       [(and (is-a? x functionable<%>) (not (object? v)))
        (send x ->rel v this)]
       [(and (is-a? v functionable<%>) (not (object? x)))
        (send v ->rel x this)]
       [(var? x) 
        (send this add-store 
              (new this% [subst (cons (cons x v) subst)]))]
       [(var? v)
        (send this add-store
              (new this% [subst (cons (cons v x) subst)]))]
       [(and (pair? x) (pair? v))
        (send (unify (car x) (car v)) unify (cdr x) (cdr v))]
       [(tree? x)
        (tree-unify x v)]
       [(tree? v)
        (tree-unify v x)]
       [(equal? x v) this]
       [else (new fail% [trace `(unify ,x ,v)])]))

    ;; t is a tree
    (define (tree-unify t v)
      (cond
       [(not (or (var? v) (tree? v) (pair? v) (null? v))) 
        (new fail% [trace `(unify ,t ,v)])]
       [(null? v)
        (for/fold ([state this]) ([node (tree-nodes t)])
          (send state unify node '()))]
       [(equal? t v) this]
       [else (new fail% [trace `(unify ,t ,v)])]))

    (define/public (add-subst state)
      (for/fold 
        ([state state])
        ([p subst])
        (send state associate (car p) (cdr p))))

    (define/public (add-store state)
      (for/fold
        ([state (add-subst state)])
        ([thing store])
        (send thing run state)))

    (define/public (run state)
      (add-store (add-subst state)))

    (define/public (combine state)
      (run state))

    (define/public (update state^)
      (define updated-subst
        (for/fold
          ([state (new this%)])
          ([p subst])
          (send state associate 
                (send state^ walk (car p))
                (send state^ walk (cdr p)))))
      (define updated-store
        (for/fold
          ([state updated-subst])
          ([thing store])
          (send (send thing update state^) combine state)))
      updated-store)

    (define/public (augment-stream stream)
      (for/fold
        ([stream (stream-map (lambda (state) (add-subst state))
                             stream)])
        ([thing store])
        (stream-filter
         (compose not (curryr is-a? fail%))
         (send thing augment-stream stream))))

    (define/public (trivial?)
      (and (null? subst) (null? store)))
    (define/public (fail?) #f)))

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

(define fail%
  (class* state% (printable<%>)
    (init-field [trace #f])
    (super-new)

    (define sexp-me `(fail% . ,(if trace (list trace) (list))))
    (define/override (custom-print p depth)
      (display sexp-me p))
    (define/override (custom-write p)
      (write sexp-me p))
    (define/override (custom-display p) 
      (display sexp-me p))

    (define/override (narrow [n #f]) '())
    (define/override (associate x v [scope '()]) this)
    (define/override (unify x v) this)
    (define/override (set-stored attr) this)
    (define/override (run state) this)
    (define/override (add-store store) this)
    (define/override (fail?) #t)
    (define/override (update state) this)
    (define/override (combine state) this)
    (define/override (trivial?) #f)))

(define fail (new fail%))

(define succeed (new state%))

;; =============================================================================
;; existentials

(provide exists fresh)

(define-syntax-rule (exists (x ...) bodys ... body)
  (let ([x (var 'x)] ...)
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
  (let ([x (eigen 'x)] ...) 
    (unless (void? bodys)
      (error 'forall "intermediate expression was not void\n ~a" 'bodys))
    ... 
    (send body add-scope (list x ...))))

;; -----------------------------------------------------------------------------
;; conjunction

(define conj%
  (class* operator% (printable<%>)
    (super-new)
    (init-field [clauses '()])
    
    (define/public (custom-print p depth)
      (display (cons (object-name this%) clauses) p))
    (define/public (custom-write p)
      (write   (cons (object-name this%) clauses) p))
    (define/public (custom-display p) 
      (display (cons (object-name this%) clauses) p))

    (define/public (run state)
      (for/fold ([state state]) ([thing clauses])
        (send thing run state)))
    
    (define/public (combine state)
      (for/fold ([state state]) ([thing clauses])
        (send thing combine state)))

    (define/public (update state^)
      (send (run (new state%)) update state^))

    (define/public (add-scope ls)
      (define new-clauses 
        (map (lambda (thing) (send thing add-scope ls)) clauses))
      (new conj% [clauses new-clauses]))))

(define (conj . clauses)
  (new conj% [clauses clauses]))

(define empty-state (new state%))

;; -----------------------------------------------------------------------------
;; disjunction

(define disj%
  (class* operator% (printable<%>)
    (init-field [states '()] [ctx #f])
    (super-new)

    (define/public (custom-print p depth)
      (display (cons (object-name this%) states) p))
    (define/public (custom-write p)
      (write   (cons (object-name this%) states) p))
    (define/public (custom-display p) 
      (display (cons (object-name this%) states) p))

    (unless (> (length states) 1)
      (error 'disj% "invalid states: ~a" states))

    (unless (andmap (lambda (ss) (is-a? ss state%)) states)
      (error 'disj% "invalid states: ~a" states))

    (define/public (update state)
      (define result 
        (filter (lambda (state) (not (is-a? state fail%)))
                (map (lambda (ss) (send ss update state))
                     states)))
      (cond
       [(null? result) fail]
       [(findf (lambda (ss) (send ss trivial?)) result) succeed]
       [(null? (cdr result)) (car result)]
       [else (new disj% [states result])]))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (augment-stream stream)
      (stream-interleave
       (stream-map (lambda (state) (send state augment-stream stream))
                   states)))

    (define/public (add-scope ls)
      (new disj% [states (map (lambda (ss) (send ss add-scope ls)) states)]))))

(define (disj . clauses)
  (define result 
    (filter (lambda (state) (not (is-a? state fail%)))
            (map (lambda (c) (send c run (new state%)))
                 clauses)))
  (cond
   [(null? result) (new fail% [trace `(disj . ,clauses)])]
   [(findf (lambda (ss) (send ss trivial?)) result) succeed]
   [(null? (cdr result)) (car result)]
   [else (new disj% [states result])]))

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

    (define/augment (update state)
      (let ([x (send state walk x)])
        (cond
         [(null-dom? x) (new fail% [trace this])]
         [(value-dom? x)
          (or (and (memv-dom? x d) state)
              (new fail% [trace this]))]
         [(singleton-dom? d)
          (== x (singleton-element-dom d))]
         [else (new dom% [rands (list x d)])])))

    ;; this is the "newer" attr, attr^ was stored before
    (define/public (merge attr^ state)
      (define old-d (send attr^ get-value))
      (define new-d (intersection-dom d old-d))
      (cond
       [(equal? new-d old-d) (send state set-stored attr^)]
       [else
        (define-values (store store^)
          (partition (curryr is-a? +%) (get-field store state)))
        (send (apply conj store)
              run
              (send (new dom% [rands (list x new-d)])
                    run (new state%
                             [subst (get-field subst state)]
                             [store store^])))]))

    (define/override (augment-stream stream)
      (send (apply disj (for/list ([i (dom->list d)]) (≡ x i)))
            augment-stream stream))))

(define (dom/a x d)
  (new dom% [rands (list x d)]))

(define (+@ . n*)
  (new +% [rands n*]))

(define +%
  (class* constraint% (functionable<%>)
    (super-new)
    (inherit-field [n* rands])

    (define/augment (update state)
      (cond
       [(or (null? n*) (null? (cdr n*))) 
        (new state%)]
       [(null? (cddr n*))
        (== (car n*) (cadr n*))]
       [(null? (cdddr n*))
        (apply update/3 state n*)]
       [else
        (match-define (list n1 n2 rest ...) n*)
        (send
         (exists (n^)
           (conj (+@ n1 n2 n^)
                 (apply +@ (cons n^ rest))))
         update state)]))

    (define (update/3 state u v w)
      (let ([u (send state walk u)]
            [v (send state walk v)]
            [w (send state walk w)])
        (cond
         [(or (var? u) (var? v) (var? w))
          (let ([du (or (send state get-stored dom% u) 
                      (and (value-dom? u) (range-dom u u))
                      (range-dom 0 100))]
              [dv (or (send state get-stored dom% v) 
                      (and (value-dom? v) (range-dom v v))
                      (range-dom 0 100))]
              [dw (or (send state get-stored dom% w) 
                      (and (value-dom? w) (range-dom w w))
                      (range-dom 0 100))])
          (let ([wmin (min-dom dw)] [wmax (max-dom dw)]
                [umin (min-dom du)] [umax (max-dom du)]
                [vmin (min-dom dv)] [vmax (max-dom dv)])
            (let ([new-w-dom (range-dom (+ umin vmin) (+ umax vmax))]
                  [new-u-dom (range-dom (- wmin vmax) (- wmax vmin))]
                  [new-v-dom (range-dom (- wmin umax) (- wmax umin))])
              (conj (+@ u v w)
                    (send (conj (dom/a w new-w-dom)
                                (dom/a v new-v-dom)
                                (dom/a u new-u-dom))
                          update state)))))]
         [(and (number? u) (number? v) (number? w))
          (or (and (= (+ u v) w) (new state%)) 
              (new fail% [trace this]))]
         [else (new fail% [trace this])])))

    ;; (+@ n*) = out
    (define/public (->out state k)
      (let ([n* (send state walk n*)])
        (cond
         [(andmap number? n*) (apply + n*)]
         [else 
          (define-values (m* x*) (partition number? n*))
          (new this% [rands (cons (apply + m*) x*)])])))

    (define/public (->rel n^ state)
      (let ([n* (send state walk n*)])
        (send (apply +@ (append n* (list n^))) run state)))))

(define tree%
  (class unary-attribute%
    (super-new)

    (inherit-field rands)

    (define/augride (update state)
      (let* ([t (send state walk (car rands))])
        (cond
         [(list? t) 
          (send (new list% [rands (list t)]) update state)]
         [(send state has-stored (list/a t)) succeed]
         [(tree? t)
          (match-define (tree nodes) t)
          (send
           (apply conj (for/list ([node nodes]) (tree/a node)))
           update state)]
         [(var? t) this]
         [else fail])))))

(define (tree/a t)
  (new tree% [rands (list t)]))

(define (partial-attribute-mixin %)
  (class* % (printable<%>)
    (super-new)
    (inherit-field rands)
    (init-field [partial #f])

    (define sexp-me 
      (cons (object-name this%) 
            (append rands (if partial (list partial) (list)))))
    (define/override (custom-print p depth)
      (display sexp-me p))
    (define/override (custom-write p)
      (write   sexp-me p))
    (define/override (custom-display p) 
      (display sexp-me p))

    (define/override (update-rands rands)
      (new this% [rands rands] [partial partial]))

    (define/public (update-partial partial)
      (new this% [rands rands] [partial partial]))

    (define/override (update state)
      (define new-partial
        (or partial (send this body . rands)))
      (define result (send new-partial update state))
      (cond
       [(is-a? result disj%)
        (send this update-partial result)]
       [else result]))))

(define list%
  (partial-attribute-mixin
   (class tree%
     (super-new)
     (define/public (body ls)
       (disj (==> (shape ls (list)))
             (==> (shape ls (cons (any) (any)))
                  (list/a (cdr@ ls))))))))

(define (list/a ls)
  (new list% [rands (list ls)]))

(define ==>%
  (class* operator% (equal<%> printable<%>)
    (super-new)
    (init-field test consequent)

    (define/public (custom-print p depth)
      (display (list (object-name this%) test consequent) p))
    (define/public (custom-write p)
      (write   (list (object-name this%) test consequent) p))
    (define/public (custom-display p) 
      (display (list (object-name this%) test consequent) p))

    (define/public (equal-to? obj recur?)
      (and (recur? test (get-field test obj))
           (recur? consequent (get-field consequent obj))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code test) (hash-code consequent)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (+ (hash-code test) (* 10 (hash-code consequent))))

    (define/public (update state)
      (define test^ (send test update state))
      (cond
       [(send test^ trivial?) 
        (send consequent update state)]
       [(send test^ fail?) test^]
       [else (new ==>% [test test^] [consequent consequent])]))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (augment-stream stream)
      (error '==>% "trying to augment: ~a\n" this))

    (define/public (add-scope ls)
      (new this%
           [test (send test add-scope ls)]
           [consequent (send consequent add-scope ls)]))))

(define (==> t [c succeed]) 
  (new ==>% 
       [test (send t run (new state%))]
       [consequent c]))

(define shape%
  (class constraint%
    (super-new)
    (inherit-field rands)
    (match-define (list x t) rands)

    (define/augment (update state)
      (let ([x (send state walk x)]
            [t (send state walk t)])
        (cond
         [(any? t) state]
         [(and (pair? x) (pair? t))
          (send (conj (shape (car x) (car t))
                      (shape (cdr x) (cdr t)))
                update state)]
         [(symbol? t) (== x t)]
         [(null? t) (== x `())]
         [(and (not (var? x)) (pair? t)) 
          (new fail% [trace this])]
         [else (shape x t)])))))

(define (shape x t) (new shape% [rands (list x t)]))

(define dots%
  (class list%
    (super-new)
    (define/override (body ls fn)
      (disj (==> (shape ls (list)))
            (==> (shape ls (cons (any) (any)))
                 (conj (fn (car@ ls)) (dots/a fn (cdr@ ls))))))))

(define (dots/a fn ls)
  (new dots% [rands (list ls fn)]))

(define length%
  (class binary-attribute%
    (super-new)
    (inherit-field rands)
    (define x (car rands))

    (define/augment (update state)
      (cond
       [(send state get-stored this% x)
        => (lambda (n) (== (cadr rands) n))]
       [else
        (let ([x (send state walk x)]
              [n (send state walk (cadr rands))])
          (cond
           [(and (list? x) (number? n))
            (or (and (= (length x) n) succeed) fail)]
           [(list? x)
            (== (length x) n)]
           [(tree? x)
            (match-define (tree nodes) x)
            (define n* 
              (for/list ([node nodes]) (var (gensym 'n))))
            (send (apply conj 
                         (apply +@ (append n* (list n)))
                         (for/list ([node nodes] [n n*])
                           (length/a node n)))
                  update state)]
           [(number? n)
            (== (for/list ([i n]) (var (gensym 'i))) x)]
           [else (conj (tree/a x) (new this% [rands (list x n)]))]))]))
    
    (define/public (get-value)
      (cond
       [(null? (cdr rands))
        (if (list? x) (length x) (range-dom 0 100))]
       [else (cadr rands)]))))

(define (length/a ls n) (new length% [rands (list ls n)]))

(define (run obj [n #f])
  (cond
   [(send (conj obj) run (new state%))
    => (lambda (state) (send state narrow n))]
   [else '()]))

(define cdr%
  (class* constraint% (functionable<%>)
    (super-new)
    (inherit-field rands)

    (define ls (car rands))

    (define/public (->out state k)
      (let ([ls (send state walk
                      ((update-functionable state k) ls))])
        (cond
         [(pair? ls) (cdr ls)]
         [(not (or (object? ls) (var? ls))) 
          (k (new fail% [trace this]))]
         [else (cdr@ ls)])))

    (define/public (->rel v state)
      (send (cdr@ ls v) update state))

    (define/augment (update state)
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) (== (cdr ls) out)]
         [else (cdr@ ls out)])))))

(define (cdr@ . rands)
  (new cdr% [rands rands]))

(define car%
  (class* constraint% (functionable<%>)
    (super-new)
    (inherit-field rands)

    (define ls (car rands))

    (define/public (->out state k)
      (let ([ls (send state walk ((update-functionable state k) ls))])
        (cond
         [(pair? ls) (car ls)]
         [(not (or (var? ls) (object? ls))) 
          (k (new fail% [trace this]))]
         [else (car@ ls)])))

    (define/public (->rel v state)
      (let ([ls (send state walk ls)])
        (send (car@ ls v) run state)))

    (define/augment (update state)
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) (== (car ls) out)]
         [else (car@ ls out)])))))

(define (car@ . rands)
  (new car% [rands rands]))

(define (partial-mixin %)
  (class* % (printable<%>)
    (super-new)
    (inherit-field rands)
    (init-field [partial #f])

    (define/override (custom-print p depth)
      (display (list (object-name this%) rands partial) p))
    (define/override (custom-write p)
      (write   (list (object-name this%) rands partial) p))
    (define/override (custom-display p) 
      (display (list (object-name this%) rands partial) p))

    (define/public (update-partial partial)
      (new this% [rands rands] [partial partial]))

    (define/augride (update state)
      (define new-partial
        (or partial (send this body . rands)))
      (define result (send new-partial update state))
      (cond
       [(is-a? result disj%)
        (send this update-partial result)]
       [else result]))))

(define-syntax (define@ stx)
  (syntax-parse stx
    [(define@ (name@ args ...) interp)
     (define name%
       (quasisyntax/loc #'name
         (partial-mixin
          (class constraint%
            (super-new)
            (define/public (body args ...) interp)))))
     #`(define (name@ args ...)
         (new #,name% [rands (list args ...)]))]))

(define (filter* f t)
  (cond
   [(f t) (list t)]
   [(pair? t) (append (filter* f (car t)) (filter* f (cdr t)))]
   [else (list)]))

(define-syntax (query stx)
  (syntax-parse stx
    [(query (x) body)
     #'(run (exists (x) (send body term-query x)))]
    [(query (x ...) body)
     #'(run (exists (x ...) (send body term-query (list x ...))))]))
