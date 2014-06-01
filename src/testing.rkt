#lang racket/base

(require racket/engine
         (except-in rackunit fail)
         "base.rkt" "main.rkt"
         racket/format)

(require (for-syntax racket/base syntax/parse))
(provide check-quick-termination
         check-long-termination
         check-one-answer
         check-run-succeed
         check-run-fail
         define-dependency-test
         (except-out (all-from-out rackunit)))

(define finished (make-parameter '()))

(define-syntax-rule (define-dependency-test name (dependencies ...) tests ...)
  (define (name)
    (unless (memq 'dependencies (finished))
      (error 'name "dependency ~a missing" 'dependencies))
    ...
    (if (memq 'name (finished))
        (test-case (~a 'name))
        (test-case (~a 'name) tests ... 
                   (finished (cons 'name (finished)))
                   (printf "finished ~a\n" 'name)))))

(define-simple-check (check-termination bool) bool)

(define-syntax (check-termination-macro stx)
  (syntax-parse stx
    [(check-termination-macro num expr)
     #`(with-check-info
        (['call 'expr] ['ticks num])
        #,(quasisyntax/loc stx
            (check-termination 
             (engine-run num (engine (lambda (y) expr))))))]))

(define-syntax-rule (check-quick-termination expr)
  (check-termination-macro 100 expr))
(define-syntax-rule (check-long-termination expr)
  (check-termination-macro 10000 expr))

(define-simple-check (check-one-answer expr)
  (= 1 (length (run expr 2))))

(define-simple-check (check-run-succeed expr)
  (equal? (run expr) (run succeed)))

(define-simple-check (check-run-fail expr)
  (equal? (run expr) (run fail)))



