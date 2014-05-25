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
         "base.rkt")

(provide (all-from-out "data.rkt")
         (all-from-out "states.rkt")
         (all-from-out "operators.rkt")
         (all-from-out "interfaces.rkt")
         (all-from-out "base.rkt")
         (all-defined-out))

(define (run obj [n #f])
  (cond
   [(send (conj obj) run (new state%))
    => (lambda (state) (send state narrow n))]
   [else '()]))

(define-syntax (query stx)
  (syntax-parse stx
    [(query (x) body)
     #'(run (exists (x) (send body term-query x)))]
    [(query (x ...) body)
     #'(run (exists (x ...) (send body term-query (list x ...))))]))

(define-syntax (define@ stx)
  (syntax-parse stx
    [(define@ (name@ args ...) interp)
     #`(define (name@ args ...)
         (define name%
           (partial-mixin
            (class relation%
              (super-new)
              (define/public (body args ...) interp))))
         (new name% [rands (list args ...)]))]))


