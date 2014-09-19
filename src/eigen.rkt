#lang racket/base

(require racket/set racket/list)
(require "data.rkt")
(provide check-scope? related-to)

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

