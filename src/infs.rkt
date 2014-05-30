;; Copyright (C) 2013-2014 Claire Alvis
;; Copyright (C) 2011-2013 Daniel P. Friedman, Oleg Kiselyov,
;; Claire E. Alvis, Jeremiah J. Willcock, Kyle M. Carter, William E. Byrd
;;
;; Permission is hereby granted, free of charge, to any person
;; obtaining a copy of this software and associated documentation
;; files (the "Software"), to deal in the Software without
;; restriction, including without limitation the rights to use, copy,
;; modify, merge, publish, distribute, sublicense, and/or sell copies
;; of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:
;;
;; The above copyright notice and this permission notice shall be
;; included in all copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
;; BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
;; ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
;; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

#lang racket/base

(require (for-syntax racket/base syntax/parse)
         racket/class)

(provide (all-defined-out))

(define mzerof (lambda () #f))
(define choiceg cons)

;; the failure value
(define mzerom (mzerof))

(define mplusm
  (lambda (a-inf f)
    (case-inf a-inf
      (() (f))
      ((f^) (delay (mplusm (f) f^)))
      ((a) (choiceg a f))
      ((a f^) (choiceg a (delay (mplusm (f) f^)))))))

;; applies a goal to an a-inf and returns an a-inf
(define (bindm a-inf fn)
  (case-inf a-inf
            [() (mzerof)]
            [(f) (delay (bindm (f) fn))]
            [(thing) (fn thing)]
            [(thing f) (mplusm (fn thing)
                               (delay (bindm (f) fn)))]))

;; macro that delays expressions
(define-syntax (lambdaf@ stx)
  (syntax-parse stx
    [(lambdaf@ () e) 
     (syntax/loc stx (lambda () e))]))

;; delays an expression
(define-syntax delay
  (syntax-rules ()
    [(_ e) (lambdaf@ () e)]))

(define empty-f (delay (mzerof)))

;; convenience macro for dispatching on the type of a-inf
(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((a^) e2) ((a f) e3))
     (let ([a-inf e])
       (cond
        [(not a-inf) e0]
        [(and (object? a-inf) (send a-inf fail?))
         e0]
        [(procedure? a-inf) 
         (let ([f^ a-inf]) e1)]
        [(not (and (pair? a-inf) (procedure? (cdr a-inf))))
         (let ([a^ a-inf]) e2)]
        [else (let ([a (car a-inf)] [f (cdr a-inf)]) e3)])))))


