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

(require (for-syntax racket/base syntax/parse))
(require racket/class 
         (except-in racket/match ==)
         racket/list
         racket/function
         racket/pretty
         racket/stream)

(require "data.rkt"
         "states.rkt"
         "interfaces.rkt"
         "operators.rkt" 
         "base.rkt"
         "infs.rkt")

(provide (all-from-out "data.rkt")
         (all-from-out "states.rkt")
         (all-from-out "operators.rkt")
         (all-from-out "interfaces.rkt")
         (all-from-out "base.rkt")
         (all-defined-out))

(define (run obj [n #f] [term #f])
  (cond
   [(send (conj obj) all (new state%))
    => (lambda (a-inf)
         (let take ([n n] [f a-inf])
           (cond
            [(and n (zero? n)) '()]
            [else
             (case-inf (f)
                       [() (list)]
                       [(f) (take n f)]
                       [(state) 
                        (list (if term (send state reify term) state))]
                       [(state f) 
                        (cons (if term (send state reify term) state)
                              (take (and n (sub1 n)) f))])])))]))

(define-syntax (query stx)
  (syntax-parse stx
    [(query (~optional n #:defaults ([n #'#f])) (x:id) body:expr)
     #'(let ([x (var 'x)])
         (run (conj body) n x))]
    [(query (~optional n #:defaults ([n #'#f])) (x:id ...) body:expr)
     #'(query (q) (exists (x ...) (conj (== q (list x ...)) body)))]))

(define-syntax (define@ stx)
  (syntax-parse stx
    [(define@ (name@ args ...) interp)
     #`(define name@ (lambda@ #:name name@ (args ...) interp))]))


