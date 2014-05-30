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
         "states.rkt"
         "data.rkt"
         "operators.rkt"
         "infs.rkt")
(provide (all-defined-out))

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
      (cons (send this get-sexp-rator) rands))
    (define/public (custom-print p depth)
      (display (sexp-me) p))
    (define/public (custom-write p)
      (write   (sexp-me) p))
    (define/public (custom-display p) 
      (display (sexp-me) p))

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
                      (send (send this update-rands (reverse new-rands))
                            run state)))]
            [else (send this run state)])))))

    (define/public (merge obj state)
      (cond
       [(is-a? obj this%) (send state set-stored obj)]
       [else (send state set-stored this)]))

    (define/public (combine state)
      (cond
       [(send state has-stored this)
        => (lambda (this^)
             (send this merge this^ (send state remove-stored this^)))]
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
    (inherit-field rands)
    (init-field [partial #f])

    (define/override (sexp-me) 
      (cons (send this get-sexp-rator) 
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
        (send this update-partial result)]
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
          (send
           (== (with-handlers 
                 ([exn:fail? (lambda (e) (new fail% [trace (object-name e)]))])
                 (apply prim (reverse (cdr rrands))))
               (car rrands))
           update state)])))))

(define (car@ . rands)
  (new (functionable-constraint% car) 
       [rands rands]))

(define (cdr@ . rands)
  (new (functionable-constraint% cdr)
       [rands rands]))

