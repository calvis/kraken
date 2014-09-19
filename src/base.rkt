;; Copyright (C) 2014 Claire Alvis
;;
;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.
;; 
;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.
;; 
;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see
;; <http://www.gnu.org/licenses/>.

#lang racket/base

(require racket/class
         racket/function
         racket/stream
         racket/list
         (except-in racket/match ==))
(require "interfaces.rkt"
         "data.rkt"
         "infs.rkt")
(provide (all-defined-out))

(require racket/class
         racket/function
         racket/stream
         racket/list
         racket/set
         racket/pretty)

(require (for-syntax racket/base syntax/parse))

(require "data.rkt"
         "interfaces.rkt"
         "infs.rkt")

(provide (all-defined-out))

(define state%
  (class* object% (equal<%> printable<%>)
    (super-new)

    (init-field [subst '()] [store '()] [eigen #f])

    (define (idemize subst)
      (map (lambda (p) (list (car p) (walk/internal (cdr p) subst))) subst))

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

    (unless (andmap object? store)
      (error 'state% "bad store\n store: ~a" store))

    (define/public (get-eigen) eigen)
    (define/public (set-eigen) 
      (new this% [subst subst] [store store] [eigen #t]))
    
    (define/public (equal-to? obj recur?)
      (and (is-a? obj this%)
           (recur? (sort (idemize subst) <
                         #:key (compose equal-hash-code car))
                   (sort (idemize (get-field subst obj)) <
                         #:key (compose equal-hash-code car)))
           (recur? store (get-field store obj))))

    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code subst) (hash-code store)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (+ (hash-code subst) (* 10 (hash-code store))))

    (define/public (add-scope ls)
      (for/fold
        ([state (new this% [subst subst] [eigen eigen])])
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
      (new this% 
           [subst subst]
           [store (cons thing store)]
           [eigen eigen]))

    (define/public (reify v)
      (let ([v (walk v)])
        (walk/internal v (reify-s v '()))))

    (define/public (associate x v [scope '()])
      (let ([x (walk x)] [v (walk v)])
        (let ([state (unify x v)])
          (cond
           [(send state get-eigen)
             (define-values (e* x*)
               (partition eigen? (related-to 
                                  (filter* cvar? (cons x v)) subst)))
             (cond
              [(check-scope? e* x* scope) state]
              [else (new fail% [trace `(eigen ,x ,v)])])]
           [else state]))))

    (define/public (unify x v)
      (cond
       [(eq? x v) this]
       [(and (is-a? x functionable<%>) (not (object? v)))
        (send x ->rel v this)]
       [(and (is-a? v functionable<%>) (not (object? x)))
        (send v ->rel x this)]
       [(var? x)
        (add-store 
         (new this%
              [subst (cons (cons x v) subst)]
              [eigen (or eigen (any/eigen? v))]))]
       [(var? v)
        (add-store
         (new this% 
              [subst (cons (cons v x) subst)]
              [eigen (or eigen (any/eigen? x))]))]
       [(and (pair? x) (pair? v))
        (send (unify (car x) (car v)) unify (cdr x) (cdr v))]
       [(tree? x)
        (send (send (unify-tree@ x v) update this)
              combine this)]
       [(tree? v)
        (send (send (unify-tree@ v x) update this)
              combine this)]
       [(equal? x v) this]
       [else (new fail% [trace `(unify ,x ,v)])]))

    (define/public (add-subst state)
      (for/fold 
        ([state (if eigen (send state set-eigen) state)])
        ([p subst])
        ;; (send-generic state state-associate (car p) (cdr p))
        (send state associate (car p) (cdr p))))

    (define/public (add-store state)
      (for/fold
        ([state state])
        ([thing store])
        (send (send thing update state) combine state)))

    (define/public (run state)
      (add-store (add-subst state)))

    (define/public (combine state)
      (run state))

    (define/public (update state^)
      (define updated-subst
        (for/fold
          ([state (new this% [eigen eigen])])
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

    (define/public (trivial?)
      (and (null? subst) (null? store)))

    (define/public (fail?) #f)

    ;; allows final computations to happen
    (define/public (augment [state #f])
      (delay
        (for/fold 
          ([a-inf (or (and state (add-subst state)) 
                      (new this% [subst subst] [eigen eigen]))])
          ([thing store])
          (bindm a-inf (lambda (state) 
                         (delay (send thing augment state)))))))))

(define state-associate (generic state% associate))

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

    (define sexp-me
      (cons (object-name this%)
            (if trace (list trace) (list))))

    (define/override (custom-print p depth)
      (display sexp-me p))
    (define/override (custom-write p)
      (write sexp-me p))
    (define/override (custom-display p) 
      (display sexp-me p))

    (define/override (augment state) this)
    (define/override (associate x v [scope '()]) this)
    (define/override (unify x v) this)
    (define/override (set-stored attr) this)
    (define/override (run state) #f)
    (define/override (add-store store) this)
    (define/override (fail?) #t)
    (define/override (update state) this)
    (define/override (combine state) this)
    (define/override (trivial?) #f)))

(define succeed (new state%))
(define fail (new fail%))

(define (filter-not-fail stream)
  (stream-filter (compose not (curryr is-a? fail%)) stream))

;; =============================================================================
;; Base is a (new base% [rands [List-of Value]])

(define base%
  (class* object% (printable<%>
                   runnable<%>
                   updateable<%>
                   combineable<%>)
    (super-new)

    (init-field [rator this%] [rands '()] [scope '()])

    (define/public (get-rator) this%)
    (define/public (get-rands) rands)
    (define/public (get-sexp-rator) (object-name this%))

    (define/public (sexp-me)
      (cons (get-sexp-rator) rands))
    (define/public (custom-print p depth)
      (display (sexp-me) p))
    (define/public (custom-write p)
      (write   (sexp-me) p))
    (define/public (custom-display p) 
      (display (sexp-me) p))

    (define/public (update-rands rands)
      (new this% [rands rands] [scope scope]))

    (define/public (run state)
      (send (update state) combine state))

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

    (define/public (augment state)
      (call/cc 
       (lambda (k)
         (let ([rands (map (update-functionable state k) rands)])
           (cond
            [(findf (curryr is-a? functionable<%>) rands)
             (define-values (a-inf new-rands)
               (for/fold ([a-inf state] [rands '()]) ([r rands])
                 (cond
                  [(is-a? r functionable<%>)
                   (let ([out (var 'out)])
                     (values (bindm a-inf
                                    (lambda (state)
                                      (send r ->rel out state)))
                             (cons out rands)))]
                  [else (values state (cons r rands))])))
             (bindm a-inf
                    (lambda (state)
                      (send (update-rands (reverse new-rands))
                            run state)))]
            [else (run state)])))))

    (define/public (merge obj state)
      (cond
       [(is-a? obj this%) (send state set-stored obj)]
       [else (send state set-stored this)]))

    (define/public (combine state)
      (cond
       [(send state has-stored this)
        => (lambda (this^)
             (merge this^ (send state remove-stored this^)))]
       [else (send state set-stored this)]))))

(define ((update-functionable state k) r)
  (if (is-a? r functionable<%>) (send r ->out state k) r))

;; -----------------------------------------------------------------------------

(define relation% 
  (class* base% (equal<%>)
    (super-new)
    (inherit-field rands)

    (define/public (equal-to? obj recur?)
      (and (is-a? obj this%)
           (is-a? this (send obj get-rator))
           (= (length rands) (length (get-field rands obj)))
           (andmap recur? rands (get-field rands obj))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code rands)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    rands (range 0 (length rands)))))))

;; -----------------------------------------------------------------------------

(define attribute%
  (class* base% (equal<%>)
    (super-new)
    (inherit-field rands)

    (define/public (equal-to? obj recur?)
      (eq? (car rands) (car (get-field rands obj))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code rands)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    rands (range 0 (length rands)))))))

;; =============================================================================
;; partial-attribute-mixin

(define (partial-attribute-mixin %)
  (class % 
    (super-new)
    (inherit get-sexp-rator)
    (inherit-field rands)
    (init-field [partial #f])

    (define/override (sexp-me) 
      (cons (get-sexp-rator) 
            (append rands (if partial (list partial) (list)))))

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
        (update-partial result)]
       [else result]))))

;; =============================================================================
;; ground@ 

(define ground%
  (class attribute% 
    (super-new)
    (inherit-field rands)
    (define/overment (merge obj state)
      (cond
       [(is-a? this (send obj get-rator))
        (inner (super merge obj state) merge obj state)]
       [(is-a? obj this%)
        (send obj merge this state)]
       [else (new fail%)]))))

;; -----------------------------------------------------------------------------

(define (ground-type-mixin pred?)
  (class ground%
    (super-new)
    (inherit-field rands)
    (define/override (get-sexp-rator)
      (object-name pred?))
    (define/augride (update state)
      (let ([x (send state walk (car rands))])
        (cond
         [(var? x) (new this% [rands (list x)])]
         [else (with-handlers 
                 ([exn:fail? (lambda (e) (new fail% [trace e]))])
                 (if (pred? x) succeed fail))])))))

;; -----------------------------------------------------------------------------

(define symbol% (ground-type-mixin symbol?))
(define number% (ground-type-mixin number?))

(define (symbol@ x) (new symbol% [rands (list x)]))
(define (number@ x) (new number% [rands (list x)]))

;; =============================================================================
;; tree@
;; x is a tree iff it implements gen:tree

(define tree%
  (class attribute%
    (super-new)
    (inherit-field rands)

    (define/augride (update state)
      (let* ([t (send state walk (car rands))])
        (cond
         [(list? t) succeed]
         [(tree? t)
          (match-define (tree nodes) t)
          (send
           (apply conj (for/list ([node nodes]) (tree@ node)))
           update state)]
         [(var? t) this]
         [else fail])))

    (define/overment (merge obj state)
      (cond
       [(or (is-a? obj this%)
            (is-a? this (send obj get-rator)))
        (inner (super merge obj state) merge obj state)]
       [else (new fail%)]))))

(define (tree@ t)
  (new tree% [rands (list t)]))

;; -----------------------------------------------------------------------------
;; list@

;; todo: list has an interpretation, but you should still be able to
;; quickly get/set it as an attribute?  and it shouldn't infinite loop
;; the projection (bc reifiable)

(define list%
  (class tree%
    (super-new)
    (define/override (get-sexp-rator) 'list@)
    (define/public (body ls)
      (project ls [(list)] [(cons a d) (list@ d)]))))

(define (list@ ls)
  (new (partial-attribute-mixin list%) [rands (list ls)]))

;; -----------------------------------------------------------------------------

(define (functionable-constraint% prim)
  (class* relation% (functionable<%>)
    (super-new)
    (inherit-field rands)

    (define/override (get-sexp-rator) 
      (object-name prim))

    (define/public (->out state k)
      (let ([rands (send state walk (map (update-functionable state k) rands))])
        (cond
         [(ormap (lambda (r) (or (var? r) (object? r))) rands) 
          (new this% [rands rands])]
         [else 
          (with-handlers 
            ([exn:fail? (lambda (e) (k (new fail% [trace (object-name e)])))])
            (apply prim rands))])))

    (define/public (->rel v state)
      (send (new this% [rands (append rands (list v))]) run state))

    (define/augment (update state)
      (let ([rands (send state walk rands)])
        (cond
         [(ormap (lambda (r) (or (var? r) (object? r))) rands)
          (new this% [rands rands])]
         [else 
          (define rrands (reverse rands))
          (call/cc
           (lambda (k)
             (send
              (== (with-handlers 
                    ([exn:fail? (lambda (e) (k (new fail% [trace (object-name e)])))])
                    (apply prim (reverse (cdr rrands))))
                  (car rrands))
              update state)))])))))

(define (car@ . rands)
  (new (functionable-constraint% car) 
       [rands rands]))

(define (cdr@ . rands)
  (new (functionable-constraint% cdr)
       [rands rands]))

(require racket/class racket/function racket/list racket/pretty racket/stream
         (except-in racket/match ==))
(require (for-syntax racket/base syntax/parse racket/syntax))
(require "data.rkt" "infs.rkt")

(provide (all-defined-out))

;; =============================================================================
;; existentials

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

(define-syntax-rule (forall (x ...) bodys ... body)
  (let ([x (eigen 'x)] ...) 
    (unless (void? bodys)
      (error 'forall "intermediate expression was not void\n ~a" 'bodys))
    ... 
    (send body add-scope (list x ...))))

;; =============================================================================
;; operators

(define operator%
  (class* object% (printable<%>)
    (super-new)

    (define/public (sexp-me) #f)

    (define/public (custom-print p depth)
      (write (sexp-me) p))
    (define/public (custom-write p)
      (write (sexp-me) p))
    (define/public (custom-display p) 
      (write (sexp-me) p))))

;; -----------------------------------------------------------------------------
;; associate

(define (≡ x v) (== x v))

(define (== x v)
  (new ==% [x x] [v v]))

(define ==%
  (class* operator% (equal<%>)
    (init-field x v [scope '()])
    (super-new)

    (define/public (equal-to? obj recur?)
      (or (and (recur? x (get-field x obj))
               (recur? v (get-field v obj)))
          (and (recur? x (get-field v obj))
               (recur? v (get-field x obj)))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code x) (hash-code v)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (+ (* 10 (hash-code x)) (* 100 (hash-code v))))

    (define/override (sexp-me)
      (list (object-name this%) x v))

    (define/public (update state)
      (let ([x (send state walk x)]
            [v (send state walk v)])
        (send ;; (send-generic (new state%) state-associate x v scope)
         (send (new state%) associate x v scope)
         update state)))

    (define/public (combine state)
      ;; (send-generic state state-associate x v scope)
      (send state associate x v scope))

    (define/public (run state)
      ;; (send-generic state state-associate x v scope)
      (send state associate x v scope))

    (define/public (add-scope ls)
      (new this% [x x] [v v] [scope (cons ls scope)]))

    (define/public (augment state)
      (delay (send (update state) augment state)))))

;; -----------------------------------------------------------------------------

(define lambda%
  (class* operator% (augmentable<%>)
    (super-new)
    (init-field sexp init [scope '()])
    (define/override (sexp-me) sexp)
    (define/public (run state)
      (send (send (init) add-scope scope) run state))
    (define/public (update state)
      this)
    (define/public (add-scope ls)
      (new this% [sexp sexp] [init init] [scope (cons ls scope)]))
    (define/public (combine state)
      (send state set-stored this))
    (define/public (augment state)
      (delay (send (send (init) add-scope scope) augment state)))))

(require (for-syntax racket/pretty))
(define-syntax (lambda@ stx)
  (syntax-parse stx
    [(lambda@
       (~optional (~seq #:name name))
       (args ...) body:expr)
     (define/with-syntax rel-name
       (cond
        [(attribute name) #'(object-name name)]
        [else #`'#,(string->symbol (pretty-format (car (syntax->list stx))))]))
     (syntax/loc stx
       (lambda (args ...)
         (let ([th (lambda () body)])
           (new lambda% [sexp (list rel-name args ...)] [init th]))))]))

(define conj%
  (class operator%
    (super-new)
    (init-field [clauses '()])

    (define/override (sexp-me)
      (cons (object-name this%) clauses))

    (define/public (run state)
      (delay (for/fold ([a-inf state]) ([g clauses])
               (bindm a-inf (lambda (state) (send g run state))))))

    (define/public (all state)
      (define (map-if-augmentable a-inf)
        (define (augment-if-augmentable state)
          (cond
           [(findf (curryr is-a? augmentable<%>)
                   (get-field store state))
            (map-if-augmentable (send state augment))]
           [else state]))
        (delay (bindm a-inf augment-if-augmentable)))
      (map-if-augmentable (run state)))
    
    (define/public (combine state)
      (for/fold ([state state]) ([thing clauses])
        (send thing combine state)))

    (define/public (update state)
      (send (new state% [store clauses]) update state))

    (define/public (add-scope ls)
      (define new-clauses
        (map (lambda (thing) (send thing add-scope ls)) clauses))
      (new conj% [clauses new-clauses]))

    (define/public (augment state)
      (delay (for/fold ([a-inf state]) ([g clauses])
               (bindm a-inf (lambda (state) (send g augment state))))))))

(define (conj . clauses)
  (new conj% [clauses clauses]))

;; -----------------------------------------------------------------------------
;; disjunction

(define disj%
  (class* operator% (equal<%> augmentable<%>)
    (init-field [states '()])
    (super-new)

    (define/override (sexp-me)
      (cons (object-name this%) states))

    (define/public (equal-to? obj recur?)
      (and (= (length states) (length (get-field states obj)))
           (andmap recur? states (get-field states obj))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code states)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    states (range 0 (length states)))))

    (define/public (update state)
      (define ss (map (lambda (ss) (send ss update state)) states))
      (define result (filter (lambda (state) (not (is-a? state fail%))) ss))
      (cond
       [(null? result) (new fail% [trace `(disj% . ,ss)])]
       [(findf (lambda (ss) (and (is-a? ss state%)
                                 (send ss trivial?)))
               result) 
        succeed]
       [(null? (cdr result)) (car result)]
       [else (new disj% [states result])]))

    (define/public (run state)
      ;; (send (update state) combine state)
      (delay (let loop ([states states])
               (cond
                [(null? (cdr states)) 
                 (send (car states) run state)]
                [else (mplusm (send (car states) run state)
                              (delay (loop (cdr states))))]))))

    (define/public (combine state)
      (cond
       [(send state has-stored this) state]
       [else (send state set-stored this)]))

    (define/public (add-scope ls)
      (new disj% [states (map (lambda (ss) (send ss add-scope ls)) states)]))

    (define/public (augment state)
      (delay 
        (let loop ([states states])
          (cond
           [(null? (cdr states)) 
            (send (car states) augment state)]
           [else (mplusm (send (car states) augment state)
                         (delay (loop (cdr states))))]))))))

(define (disj . clauses)
  (new disj% [states clauses]))

;; -----------------------------------------------------------------------------
;; not

(define not%
  (class* operator% (equal<%>)
    (super-new)
    (init-field stmt)

    (define/override (sexp-me)
      (list (object-name this%) stmt))

    (define/public (equal-to? obj recur?)
      (recur? stmt (get-field stmt obj)))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code stmt)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (hash-code stmt))

    (define/public (update state)
      (define new-stmt (send stmt update state))
      (cond
       [(is-a? new-stmt state%)
        (cond
         [(send new-stmt trivial?)
          (new fail%)]
         [(send new-stmt fail?)
          succeed]
         [else 
          (define newer-stmt
            (append (for/list ([p (get-field subst new-stmt)])
                      (! (new state% [subst `(,p)])))
                    (for/list ([thing (get-field store new-stmt)])
                      (! thing))))
          (if (= (length newer-stmt) 1)
              (new this% [stmt new-stmt])
              (apply disj newer-stmt))])]
       [(is-a? new-stmt disj%)
        (apply disj (map (lambda (state) (new this% [stmt state]))
                         (get-field states new-stmt)))]
       [else (new this% [stmt new-stmt])]))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (add-scope ls)
      (new this% [stmt (send stmt add-scope ls)]))))

(define (! stmt)
  (new not% [stmt (send stmt update (new state%))]))


;; -----------------------------------------------------------------------------

(define project%
  (class* operator% (augmentable<%>)
    (super-new)
    (init-field term pattern phase1 phase2)

    (define/override (sexp-me)
      (list (object-name this%) term pattern))

    (define/public (update state)
      (let ([t (send state walk term)])
        (cond
         [(var? t) this]
         [(phase1 t)
          => (lambda (this^)
               (cond
                [(boolean? this^) this]
                [else (send this^ update state)]))]
         [else (new fail% [trace this])])))

    (define/public (augment state)
      (let ([t (send state walk term)])
        (cond
         [(phase1 t)
          => (lambda (this^)
               (cond
                [(boolean? this^) 
                 (send (phase2 t) augment state)]
                [else 
                 (send this^ augment state)]))]
         [else 
          (send (phase2 t) augment state)])))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (add-scope ls) this)))

(require (for-syntax racket/function))

(define-for-syntax (walk-pattern stx quoted?)
  (syntax-parse stx
    [((~literal unquote) x:id)
     #:fail-unless quoted? "unquote not inside quasiquote"
     (list #'x)]
    [((~literal quasiquote) expr)
     (walk-pattern #'expr #t)]
    [((~literal cons) a d)
     (append (walk-pattern #'a quoted?)
             (walk-pattern #'d quoted?))]
    [((~literal list) . d)
     (apply append (map (curryr walk-pattern quoted?)
                        (syntax->list #'d)))]
    [((~literal tree) . d)
     (apply append (map (curryr walk-pattern quoted?)
                        (syntax->list #'d)))]
    [(a . d)
     (append (walk-pattern #'a quoted?)
             (walk-pattern #'d quoted?))]
    [x:id (if quoted? (list) (list #'x))]
    [x (list)]))

(require (for-syntax racket/pretty))

(define-for-syntax (commit-pattern stx thing quoted?)
  (syntax-parse stx
    [((~literal unquote) x:id)
     #:fail-unless quoted? "unquote not inside quasiquote"
     #'#t]
    [((~literal quasiquote) expr)
     #:when (not quoted?)
     (commit-pattern #'expr thing #t)]
    [((~literal cons) a d)
     #:when (not quoted?)
     #`(or (var? #,thing)
           (and (pair? #,thing) 
                #,(commit-pattern #'a #`(car #,thing) quoted?)
                #,(commit-pattern #'d #`(cdr #,thing) quoted?)))]
    [((~literal list))
     #`(null? #,thing)]
    [((~literal list) a d ...)
     #`(or (var? #,thing)
           (and (pair? #,thing)
                #,(commit-pattern #'(list d ...) #`(cdr #,thing) quoted?)))]
    [((~literal tree) ((~literal list) d ...))
     #:when (not quoted?)
     (define/with-syntax (node-i ...)
       (generate-temporaries #'(d ...)))
     (define/with-syntax (commit-node-i ...)
       (map (lambda (d-thing i) 
              (commit-pattern d-thing i quoted?))
            (syntax->list #'(d ...))
            (syntax->list #'(node-i ...))))
     #`(or (var? #,thing)
           (and (tree? #,thing)
                (list? (tree-nodes #,thing))
                (let-values ([(node-i ...) 
                              (apply values (tree-nodes #,thing))])
                  (and commit-node-i ...)))
           (list? #,thing))]
    [(a . d)
     #:fail-unless quoted? "expected constructor"
     #`(or (var? #,thing)
           (and (pair? #,thing) 
                #,(commit-pattern #'a #`(car #,thing) quoted?)
                #,(commit-pattern #'d #`(cdr #,thing) quoted?)))]
    [x:id
     (cond
      [quoted? #`(or (var? #,thing) (eq? #,thing 'x))]
      [else #`t])]
    [() 
     #:fail-unless quoted? "app"
     #`(or (var? #,thing) (null? #,thing))]))

(require (for-syntax racket/list))
(define-syntax (project stx)
  (syntax-parse stx
    [(project project-term:id
       [pat (~optional body #:defaults ([body #'succeed]))]
       ...)
     (define/with-syntax ((vars ...) ...)
       (map (compose
             (curryr remove-duplicates free-identifier=?)
             (curryr walk-pattern #f))
            (syntax->list #'(pat ...))))
     (define/with-syntax (hope? ...)
       (map (curryr commit-pattern #'t #f)
            (syntax->list #'(pat ...))))
     ;; support all of match and punt if it doesn't work
     (define/with-syntax (phase1-body ...)
       #'((lambda (t) (match t [pat body] [_ hope?]))
          ...))
     (define/with-syntax (phase2-body ...)
       #'((lambda (t)
            (exists (vars ...) 
              (conj (== t pat) 
                    (let ([project-term pat]) body))))
          ...))
     #'(disj
        (new project%
             [term project-term] 
             [pattern 'pat]
             [phase1 phase1-body]
             [phase2 phase2-body])
        ...)]))

(define (unify-tree@ t v)
  (new unify-tree% [rands (list t v)]))

(define unify-tree%
  (class relation%
    (super-new)
    (inherit-field rands)
    (define/augment (update state)
      (let ([t (send state walk (car rands))]
            [v (send state walk (cadr rands))])
        (cond
         [(equal? t v) succeed]
         [(pair? v)
          (send (conj (tree-first@ t (car v))
                      (tree-rest@ t (cdr v)))
                update state)]
         [(null? v)
          (match-define (tree nodes) t)
          (send
           (apply conj (for/list ([node nodes]) 
                         (== node (list))))
           update state)]
         [else (new this% [rands (list t v)])])))))

(define (tree-first@ t v)
  (new tree-first% [rands (list t v)]))

(define tree-first%
  (class* relation% (augmentable<%>)
    (super-new)
    (inherit-field rands)
    (define/augment (update state)
      (let ([t (send state walk (car rands))]
            [v (send state walk (cadr rands))])
        (match-define (tree nodes) t)
        (cond
         [(null? nodes) fail]
         [(list? (car nodes))
          (send (== (tree-first nodes) v) update state)]
         [else (new this% [rands (list t v)])])))

    (define/override (augment state)
      (let ([t (send state walk (car rands))]
            [v (send state walk (cadr rands))])
        (match-define (tree nodes) t)
        (cond
         [(null? nodes) fail]
         [(pair? (car nodes))
          (send (== (tree-first t) v) augment state)]
         [else
          (send
           (apply disj
                  (let loop ([nodes nodes] [pre '()])
                    (cond
                     [(null? nodes) (list)]
                     [else 
                      (cons (apply conj
                                   (== (car nodes) (cons v (var 'd)))
                                   (for/list ([node pre])
                                     (== node (list))))
                            (loop (cdr nodes) (cons (car nodes) pre)))])))
           augment state)])))))

(define (tree-rest@ t v)
  (new tree-rest% [rands (list t v)]))

(define tree-rest%
  (class relation%
    (super-new)
    (inherit-field rands)
    (define/augment (update state)
      (let ([t (send state walk (car rands))]
            [v (send state walk (cadr rands))])
        (match-define (tree nodes) t)
        (cond
         [(null? nodes) fail]
         [(null? (car nodes))
          (send (tree-rest@ (tree (cdr nodes)) v) update state)]
         [(pair? (car nodes))
          (send (== (tree-rest t) v) update state)]
         [else (new this% [rands (list t v)])])))))

(define/match (tree-first t)
  [[(tree (list ls rest ...))]
   (car ls)])

(define/match (tree-rest t)
  [[(tree (cons (list) rest))]
   (tree-rest rest)]
  [[(tree (cons (list a) rest))]
   (tree rest)]
  [[(tree (cons (cons a d) rest))]
   (tree (cons d rest))])

