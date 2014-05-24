#lang racket/base

(require racket/class)
(provide (all-defined-out))

(define streamable<%> (interface () augment-stream))
(define functionable<%> (interface () ->rel))


