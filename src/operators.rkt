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

(require racket/class racket/function)
(require (rename-in racket/stream [stream-append stream-append-proc]))
(require "states.rkt" "data.rkt")

(provide (except-out (all-defined-out) stream-append))

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
      (new this% [x x] [v v] [scope (cons ls scope)]))

    (define/public (augment-stream stream)
      (filter-not-fail
       (stream-map (lambda (state) (run state)) stream)))))

;; -----------------------------------------------------------------------------
;; conjunction

(define conj%
  (class* operator% (printable<%>)
    (super-new)
    (init-field [clauses '()] [query #f])
    
    (define/public (custom-print p depth)
      (display (cons (object-name this%) clauses) p))
    (define/public (custom-write p)
      (write   (cons (object-name this%) clauses) p))
    (define/public (custom-display p) 
      (display (cons (object-name this%) clauses) p))

    (define/public (run state)
      (define result
        (for/fold ([state state]) ([thing clauses])
          (send thing run state)))
      (if query (send result add-query query) result))
    
    (define/public (combine state)
      (for/fold ([state state]) ([thing clauses])
        (send thing combine state)))

    (define/public (update state^)
      (send (run (new state%)) update state^))

    (define/public (add-scope ls)
      (define new-clauses 
        (map (lambda (thing) (send thing add-scope ls)) clauses))
      (new conj% [clauses new-clauses] [query query]))
    
    (define/public (add-query t)
      (new this% [clauses clauses] [query t]))

    (define/public (augment-stream stream)
      (filter-not-fail
       (for/fold ([stream stream]) ([thing clauses])
         (send thing augment-stream stream))))))

(define (conj . clauses)
  (new conj% [clauses clauses]))

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
      (filter-not-fail
       (stream-interleave
        (stream-map (lambda (state) (send state augment-stream stream))
                    states))))

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

(define-syntax-rule (stream-append s* ... s)
  (let ([last (lambda () s)]
        [pre (stream-append-proc s* ...)])
    (define (loop stream)
      (cond
       [(stream-empty? stream) (last)]
       [else (stream-cons (stream-first stream)
                          (loop (stream-rest stream)))]))
    (loop pre)))

;; -----------------------------------------------------------------------------
;; implies

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
      (filter-not-fail
       (stream-map (lambda (state) (send consequent run state))
                   (filter-not-fail (send test augment-stream stream)))))

    (define/public (add-scope ls)
      (new this%
           [test (send test add-scope ls)]
           [consequent (send consequent add-scope ls)]))))

(define (==> t [c succeed]) 
  (new ==>% 
       [test (send t run (new state%))]
       [consequent c]))
