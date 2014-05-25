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
         "operators.rkt")
(provide (all-defined-out))

;; =============================================================================
;; Base is a (new base% [rands [List-of Value]])

(define base%
  (class* object% (printable<%> 
                   streamable<%>
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

    (define/public (augment-state state)
      (call/cc 
       (lambda (k)
         (let ([rands (map (update-functionable state k) rands)])
           (cond
            [(findf (curryr is-a? functionable<%>) rands)
             (define-values (new-state new-rands)
               (for/fold ([state state] [rands '()]) ([r rands])
                 (cond
                  [(is-a? r functionable<%>)
                   (let ([out (var 'out)])
                     (values (send r ->rel out state)
                             (cons out rands)))]
                  [else (values state (cons r rands))])))
             (send (send this update-rands (reverse new-rands))
                   run new-state)]
            [else (send this run state)])))))

    (define/public (augment-stream stream)
      (filter-not-fail       
       (stream-map (lambda (state) (augment-state state)) stream)))

    (define/public (combine state)
      (send state set-stored this))))

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
      (and (or (implementation? 
                (send obj get-rator)
                (class->interface this%))
               (implementation? 
                this%
                (class->interface (send obj get-rator))))
           (eq? (car rands) (car (get-field rands obj)))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code rands)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    rands (range 0 (length rands)))))

    (define/override (combine state)
      (cond
       [(send state has-stored this)
        => (lambda (this^)
             ;; we have two identical attributes on the same variable,
             ;; see if they need to merge and take appropriate actions
             (send this merge this^ (send state remove-stored this^)))]
       [else (send state set-stored this)]))))

(define unary-attribute%
  (class attribute% 
    (super-new)

    (define/public (merge a state)
      (cond
       [(implementation? (send a get-rator) (class->interface this%))
        (send state set-stored a)]
       [else (send state set-stored this)]))))

(define binary-attribute%
  (class attribute% 
    (super-new)))

;; -----------------------------------------------------------------------------

(define shape%
  (class relation%
    (super-new)
    (inherit-field rands)
    (match-define (list x t) rands)

    (define/augment (update state)
      (let ([x (send state walk x)]
            [t (send state walk t)])
        (cond
         [(any? t) state]
         [(and (pair? x) (pair? t))
          (send (conj (shape (car x) (car t))
                      (shape (cdr x) (cdr t)))
                update state)]
         [(symbol? t) (send (== x t) update state)]
         [(null? t) (send (== x `()) update state)]
         [(and (not (var? x)) (pair? t)) 
          (new fail% [trace this])]
         [else (shape x t)])))

    (define/override (augment-state state)
      (let loop ([x x] [t t] [state state])
        (let ([x (send state walk x)]
              [t (send state walk t)])
          (cond
           [(any? t) state]
           [(and (pair? x) (pair? t))
            (loop (cdr x) (cdr t)
                  (loop (car x) (car t) state))]
           [(symbol? t) (send state associate x t)]
           [(null? t) (send state associate x `())]
           [(and (not (var? x)) (pair? t)) 
            (new fail% [trace this])]
           [(pair? t)
            (let ([a (var 'a)] [d (var 'd)])
              (loop d (cdr t)
                    (loop a (car t) 
                          (send state associate (cons a d) x))))]
           [else (error 'shape "augment stream: ~a ~a" x t)]))))))

(define (shape x t) (new shape% [rands (list x t)]))

(define-syntax-rule (case-shape x [t clause] ...)
  (disj (==> (shape x `t) clause) ...))

(define (functionable-constraint% prim)
  (class* relation% (functionable<%>)
    (super-new)
    (inherit-field rands)

    (define/public (->out state k)
      (let ([rands (send state walk (map (update-functionable state k) rands))])
        (cond
         [(ormap (lambda (r) (or (var? r) (object? r))) rands) 
          (new this% [rands rands])]
         [else 
          (with-handlers ([exn:fail? (lambda (e) (k (new fail% [trace e])))])
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
          (with-handlers ([exn:fail? (lambda (e) (new fail% [trace e]))])
            (== (apply prim (reverse (cdr rrands))) (car rrands)))])))))

(define (car@ . rands)
  (new (functionable-constraint% car) [rands rands]))

(define (cdr@ . rands)
  (new (functionable-constraint% cdr) [rands rands]))

(define (partial-mixin %)
  (class % 
    (super-new)
    (inherit-field rands)
    (init-field [partial #f])

    (define/override (sexp-me)
      (if partial
          `(,(send this get-sexp-rator) ,@rands ,partial)
          (super sexp-me)))

    (define/public (update-partial partial)
      (new this% [rands rands] [partial partial]))

    (define/augride (update state)
      (define new-partial
        (or partial (send this body . rands)))
      (define result (send new-partial update state))
      (cond
       [(is-a? result disj%)
        (send this update-partial result)]
       [else result]))

    (define/override (augment-stream stream)
      (define new-partial (or partial (send this body . rands)))
      (send new-partial augment-stream stream))))

