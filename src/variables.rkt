#lang racket/base

(require racket/class)

;; cvars, vars, fresh, placeholders

;; =============================================================================
;; cvars

(provide (struct-out cvar) reify-n)

;; normal miniKanren vars are actually an instance of a more general
;; "constrained var", or cvar for short.
(struct cvar (str x)
        #:methods gen:custom-write
        [(define (write-proc x port mode)
           (display (format "#~a(~a)" (cvar-str x) (cvar-x x)) port))])

(define (reify-n cvar n)
  (string->symbol (format "~a.~a" (cvar-str cvar) (number->string n))))

;; =============================================================================
;; vars; A LogicVariable (LV) is a (var Symbol)

(provide var var?)

;; defines a normal miniKanren var as a cvar that is printed with "_"
(struct -var cvar ())
(define (var x) (-var "_" x))
(define (var? x) (-var? x))

;; =============================================================================
;; placeholders

(provide any any?)

(struct any () #:transparent)

