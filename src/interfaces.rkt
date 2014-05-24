#lang racket/base

(require racket/class)
(provide (all-defined-out))

(define streamable<%> (interface () augment-stream))
(define functionable<%> (interface () ->rel))
(define runnable<%> (interface () run))
(define updateable<%> (interface () update))
(define combineable<%> (interface () combine))

