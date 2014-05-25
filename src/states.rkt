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
         racket/set)

(require "data.rkt"
         "interfaces.rkt")

(provide (all-defined-out))

(define state%
  (class* object% (equal<%> printable<%>)
    (super-new)

    (init-field [subst '()] [store '()] [query #f])

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
      (define result
        (take (filter-not-fail answer-stream) n))
      (if query (map (lambda (state) (send state reify query)) result) result))

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
        ([stream (stream-map (lambda (state) (add-subst state)) stream)])
        ([thing store])
        (send thing augment-stream stream)))

    (define/public (trivial?)
      (and (null? subst) (null? store)))

    (define/public (fail?) #f)

    (define/public (add-query query)
      (new this% [subst subst] [store store] [query query]))))

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

(define (filter-not-fail stream)
  (stream-filter (compose not (curryr is-a? fail%)) stream))


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

(define (filter* f t)
  (cond
   [(f t) (list t)]
   [(pair? t) (append (filter* f (car t)) (filter* f (cdr t)))]
   [else (list)]))

