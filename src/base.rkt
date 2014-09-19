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
         racket/pretty
         (except-in racket/match ==))

(require (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     racket/pretty
                     racket/function
                     racket/list))

(require "interfaces.rkt"
         "data.rkt"
         "infs.rkt"
         "eigen.rkt")

(provide (all-defined-out))

;; =============================================================================
;; a State is a (new state% [subst Substitution] [store ConstraintStore])

(define state%
  (class* object% (equal<%> 
                   printable<%>
                   runnable<%>
                   updateable<%>
                   augmentable<%>)
    (super-new)

    ;; subst is a Substitution
    ;; store is a ConstraintStore
    ;; eigen is a Boolean - #t if eigens have been introduced, #f otherwise
    (init-field [subst '()] [store '()] [eigen #f])

    ;; -------------------------------------------------------------------------
    ;; printing

    (define (idemize subst)
      (for/list ([p subst]) 
        (list (car p) (walk/internal (cdr p) subst))))

    (define sexp-me
      (list (object-name this%) (idemize subst) store))

    (define/public (custom-print p depth) (display sexp-me p))
    (define/public (custom-write p)       (write sexp-me p))
    (define/public (custom-display p)     (display sexp-me p))

    ;; -------------------------------------------------------------------------
    ;; checking our inner values

    (unless (list? subst)
      (error 'state% "subst is not a list\n subst: ~a" subst))

    (unless (list? store)
      (error 'state% "store is not a list\n store: ~a" store))

    (unless (andmap object? store)
      (error 'state% "bad store\n store: ~a" store))

    ;; -------------------------------------------------------------------------
    ;; eigens

    (define/public (get-eigen) eigen)
    (define/public (set-eigen) (new this% [subst subst] [store store] [eigen #t]))
    
    (define/public (add-scope ls)
      (for/fold
        ([state (new this% [subst subst] [eigen eigen])])
        ([thing store])
        (send state set-stored (send thing add-scope ls))))

    ;; -------------------------------------------------------------------------
    ;; equality 

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

    ;; -------------------------------------------------------------------------
    ;; substitution

    (define/public (walk u)
      (walk/internal u subst))

    (define/public (associate x v [scope '()])
      (let ([x (walk x)] [v (walk v)])
        (define state (unify x v))
        (cond
         [(send state get-eigen)
          (define cvars (filter* cvar? (cons x v)))
          (define-values (e* x*) 
            (partition eigen? (related-to cvars subst)))
          (cond
           [(check-scope? e* x* scope) state]
           [else (new fail% [trace `(eigen ,x ,v)])])]
         [else state])))

    (define/public (unify x v)
      (cond
       [(eq? x v) this]
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
        (send state associate (car p) (cdr p))))

    (define/public (reify v)
      (let ([v (walk v)])
        (walk/internal v (reify-s v '()))))

    ;; -------------------------------------------------------------------------
    ;; constraint store

    (define/public (add-store state)
      (for/fold
        ([state state])
        ([thing store])
        (send (send thing update state) combine state)))

    (define/public (remove-stored thing)
      (new this% [subst subst] [store (remove thing store)]))

    (define/public (has-stored thing)
      (findf (curry equal? thing) store))

    (define/public (get-stored x% x)
      (define equal-attribute?
        (curry equal? (new x% [rands (list x)])))
      (cond
       ;; TODO: hack
       [(findf equal-attribute? store)
        => (lambda (attr) (send attr get-value))]
       [else #f]))

    (define/public (set-stored thing)
      (define new-store (cons thing store))
      (new this% [subst subst] [store new-store] [eigen eigen]))

    ;; -------------------------------------------------------------------------
    ;; interface

    (define/public (run state)
      (add-store (add-subst state)))

    (define/public (combine state)
      (run state))

    (define/public (update state^)
      (define init-state
        (new this% [eigen eigen]))
      (define updated-subst
        (for/fold
          ([state init-state])
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

    (define/public (augment [state #f])
      (define a-inf
        (or (and state (add-subst state))
            (new this% [subst subst] [eigen eigen])))
      (define ((send-augment thing) state)
        (send thing augment state))
      (delay
        (for/fold ([a-inf a-inf]) ([thing store])
          (bindm a-inf (send-augment thing)))))))

;; a Succeed is a (new state%)
(define succeed (new state%))

;; a Fail is a (new fail%) or (new fail% [trace Any]), where the trace
;; is an optional field that contains something relating to the cause
;; of the failure
(define fail%
  (class state%
    (init-field [trace #f])
    (super-new)

    (define sexp-me
      (cons (object-name this%) (if trace (list trace) (list))))

    (define/override (custom-print p depth) (display sexp-me p))
    (define/override (custom-write p)       (write sexp-me p))
    (define/override (custom-display p)     (display sexp-me p))

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
(define fail (new fail%))

;; =============================================================================
;; a Base is a (new base% [rands [List-of Value]])

(define base%
  (class* object% (printable<%>
                   runnable<%>
                   updateable<%>
                   combineable<%>)
    (super-new)
    (init-field [rator this%] [rands '()] [scope '()])

    ;; -------------------------------------------------------------------------
    ;; printing

    (define/public (get-rator) this%)
    (define/public (get-rands) rands)
    (define/public (get-sexp-rator) (object-name this%))

    (define/public (sexp-me) (cons (get-sexp-rator) rands))
    (define/public (custom-print p depth) (display (sexp-me) p))
    (define/public (custom-write p)       (write   (sexp-me) p))
    (define/public (custom-display p)     (display (sexp-me) p))

    ;; -------------------------------------------------------------------------
    ;; interface

    (define/public (run state)
      (send (update state) combine state))

    (define/pubment (update state)
      (inner this update state))

    (define/public (add-scope ls)
      (new this% [rands rands] [scope (cons ls scope)]))

    (define/public (merge obj state)
      (cond
       [(is-a? obj this%) (send state set-stored obj)]
       [else (send state set-stored this)]))

    (define/public (combine state)
      (cond
       [(send state has-stored this)
        => (lambda (this^)
             (merge this^ (send state remove-stored this^)))]
       [else (send state set-stored this)]))

    (define/public (augment state)
      (run state))))

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

    (define/override (update state)
      (define new-partial
        (or partial (send this body . rands)))
      (define result (send new-partial update state))
      (cond
       [(is-a? result disj%)
        (new this% [rands rands] [partial partial])]
       [else result]))))

;; =============================================================================
;; ground@ 

(define ground%
  (class attribute% 
    (super-new)
    (define/overment (merge obj state)
      (cond
       [(is-a? this (send obj get-rator))
        (inner (super merge obj state) merge obj state)]
       [(is-a? obj this%)
        (send obj merge this state)]
       [else (new fail%)]))))

;; TODO: not a mixin anymore
(define (ground-type-mixin pred?)
  (class ground%
    (super-new)
    (inherit-field rands)
    (define/override (get-sexp-rator)
      (object-name pred?))
    (define/augride (update state)
      (let ([x (send state walk (car rands))])
        (if (var? x)
            (new this% [rands (list x)])
            (with-handlers 
              ([exn:fail? (lambda (e) (new fail% [trace e]))])
              (if (pred? x) succeed fail)))))))

;; =============================================================================
;; existentials

(define-syntax-rule (exists (x ...) effect ... stmt)
  (let ([x (var 'x)] ...)
    (unless (void? effect)
      (error 'exists "not void\n expression: ~a" 'effect))
    ... 
    (send stmt add-scope (list x ...))))

(define-syntax-rule (fresh (x ...) body ...)
  (exists (x ...) body ...))

;; =============================================================================
;; universals

(define-syntax-rule (forall (x ...) effect ... stmt)
  (let ([x (eigen 'x)] ...)
    (unless (void? effect)
      (error 'forall "intermediate expression was not void\n ~a" 'effect))
    ... 
    (send stmt add-scope (list x ...))))

;; =============================================================================
;; operators

(define operator%
  (class* object% (printable<%>)
    (super-new)
    (define/public (sexp-me) #f)
    (define/public (custom-print p depth) (write (sexp-me) p))
    (define/public (custom-write p)       (write (sexp-me) p))
    (define/public (custom-display p)     (write (sexp-me) p))

    (define/public (combine state)
      (cond
       [(send state has-stored this) state]
       [else (send state set-stored this)]))))

;; -----------------------------------------------------------------------------
;; associate

(define (≡ x v) (== x v))
(define (== x v) (new ==% [x x] [v v]))

(define ==%
  (class* operator% (equal<%>)
    (init-field x v [scope '()])
    (super-new)

    ;; -------------------------------------------------------------------------
    ;; equality 

    (define/public (equal-to? obj recur?)
      (or (and (recur? x (get-field x obj))
               (recur? v (get-field v obj)))
          (and (recur? x (get-field v obj))
               (recur? v (get-field x obj)))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code x) (hash-code v)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (+ (* 10 (hash-code x)) (* 100 (hash-code v))))

    ;; -------------------------------------------------------------------------
    ;; printing
    (define/override (sexp-me)
      (list (object-name this%) x v))


    ;; -------------------------------------------------------------------------
    ;; interface

    (define/public (update state)
      (let ([x (send state walk x)]
            [v (send state walk v)])
        (send (send (new state%) associate x v scope) update state)))

    (define/override (combine state)
      (send state associate x v scope))

    (define/public (run state)
      (send state associate x v scope))

    (define/public (add-scope ls)
      (new this% [x x] [v v] [scope (cons ls scope)]))

    (define/public (augment state)
      (delay (send (update state) augment state)))))

;; -----------------------------------------------------------------------------
;; anonymous relations

(define anonymous-relation%
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
    (define/public (augment state)
      (delay (send (send (init) add-scope scope) augment state)))))

(define-syntax (relation@ stx)
  (syntax-parse stx
    [(relation@ (~optional (~seq #:name name)) (args ...) body:expr)
     (define/with-syntax rel-name
       (cond
        [(attribute name) #'(object-name name)]
        [else #`'#,(string->symbol (pretty-format (car (syntax->list stx))))]))
     (syntax/loc stx
       (lambda (args ...)
         (new anonymous-relation%
              [sexp (list rel-name args ...)]
              [init (lambda () body)])))]))

;; -----------------------------------------------------------------------------
;; conjunction

(define conj%
  (class operator%
    (super-new)
    (init-field [clauses '()])

    (define/override (sexp-me)
      (if (null? (cdr clauses))
          (send (car clauses) sexp-me)
          (cons (object-name this%) clauses)))

    (define/public (run state)
      (define ((run-state g) state) (send g run state))
      (delay (for/fold ([a-inf state]) ([g clauses]) 
               (bindm a-inf (run-state g)))))

    (define/public (all state)
      (define has-augmentable?
        (curryr is-a? augmentable<%>))
      (define (map-if-augmentable a-inf)
        (define (augment-if-augmentable state)
          (cond
           [(findf has-augmentable? (get-field store state))
            (map-if-augmentable (send state augment))]
           [else state]))
        (delay (bindm a-inf augment-if-augmentable)))
      (map-if-augmentable (run state)))
    
    (define/override (combine state)
      (for/fold ([state state]) ([thing clauses])
        (send thing combine state)))

    (define/public (update state)
      (send (new state% [store clauses]) update state))

    (define/public (add-scope ls)
      (define new-clauses
        (for/list ([thing clauses]) (send thing add-scope ls)))
      (new conj% [clauses new-clauses]))

    (define/public (augment state)
      (define ((send-augment g) state) (send g augment state))
      (delay (for/fold ([a-inf state]) ([g clauses])
               (bindm a-inf (send-augment g)))))))

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
      (define ss (for/list ([ss states]) (send ss update state)))
      (define result (filter (lambda (state) (not (is-a? state fail%))) ss))
      (cond
       [(null? result) (new fail% [trace `(disj% . ,ss)])]
       [(findf (lambda (ss) (and (is-a? ss state%)
                                 (send ss trivial?)))
               result)
        ;; could check that the rest of the states fail
        succeed]
       [(null? (cdr result)) (car result)]
       [else (new disj% [states result])]))

    (define/public (run state)
      (define (loop states)
        (cond
         [(null? (cdr states)) 
          (send (car states) run state)]
         [else (mplusm (send (car states) run state)
                       (delay (loop (cdr states))))]))
      (delay (loop states)))

    (define/public (add-scope ls)
      (new disj% [states (for/list ([ss states]) 
                           (send ss add-scope ls))]))

    (define/public (augment state)
      (define (loop states)
        (cond
         [(null? (cdr states)) 
          (send (car states) augment state)]
         [else (mplusm (send (car states) augment state)
                       (delay (loop (cdr states))))]))
      (delay (loop states)))))

(define (disj . clauses)
  (cond
   [(null? clauses) (new fail%)]
   [(null? (cdr clauses)) (car clauses)]
   [else (new disj% [states clauses])]))

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
        (apply conj (for/list ([state (get-field states new-stmt)])
                      (new this% [stmt state])))]
       [else (new this% [stmt new-stmt])]))

    (define/public (run state)
      (send (update state) combine state))

    (define/public (add-scope ls)
      (new this% [stmt (send stmt add-scope ls)]))))

(define (! stmt)
  (new not% [stmt (send stmt update (new state%))]))

;; -----------------------------------------------------------------------------
;; projection

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
               (if (boolean? this^)
                   (send (phase2 t) augment state)
                   (send this^ augment state)))]
         [else 
          (send (phase2 t) augment state)])))

    (define/public (run state)
      (send (update state) combine state))

    (define/public (add-scope ls) this)))

(define-for-syntax (walk-pattern stx quoted?)
  (syntax-parse stx
    [((~literal unquote) x:id)
     #:fail-unless quoted? "unquote not inside quasiquote"
     (list #'x)]
    [((~literal quasiquote) expr)
     (walk-pattern #'expr #t)]
    [((~literal quote) expr)
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

(define-for-syntax (commit-pattern stx thing quoted?)
  (syntax-parse stx
    [((~literal unquote) x:id)
     #:fail-unless quoted? "unquote not inside quasiquote"
     #'#t]
    [((~literal quasiquote) expr)
     #:when (not quoted?)
     (commit-pattern #'expr thing #t)]
    [((~literal quote) expr)
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
    [x
     #`(or (var? #,thing) (eq? #,thing 'x))]))

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

;; =============================================================================
;; trees

(define (tree@ t)
  (new tree% [rands (list t)]))

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
          (send (apply conj (for/list ([node nodes]) (tree@ node)))
                update state)]
         [(var? t) this]
         [else fail])))

    (define/overment (merge obj state)
      (cond
       [(or (is-a? obj this%)
            (is-a? this (send obj get-rator)))
        (inner (super merge obj state) merge obj state)]
       [else (new fail%)]))))

(define (unify-tree@ t v)
  (new unify-tree% [rands (list t v)]))

(define unify-tree%
  (class relation%
    (super-new)
    (inherit-field rands)
    (define/augment (update state)
      (define t (send state walk (car rands)))
      (define v (send state walk (cadr rands)))
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
       [else (new this% [rands (list t v)])]))))

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
  (class* relation% (augmentable<%>)
    (super-new)
    (inherit-field rands)
    (inherit run)
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

;; =============================================================================
;; convenience

