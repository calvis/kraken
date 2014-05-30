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
         (except-in racket/match ==))
(require (lib "kraken/src/main.rkt")
         (lib "kraken/lib/fd.rkt"))
(provide (all-defined-out))

;; -----------------------------------------------------------------------------
;; dots@

(define dots%
  (class list%
    (super-new)
    (define/override (get-sexp-rator) 'dots@)
    (define/override (body ls fn)
      (disj (==> (shape ls (list)))
            (==> (shape ls (cons (any) (any)))
                 (conj (fn (car@ ls)) (dots@ fn (cdr@ ls))))))))

(define (dots@ fn ls)
  (new (partial-attribute-mixin dots%) [rands (list ls fn)]))

;; =============================================================================
;; length@

(define length%
  (class tree%
    (super-new)
    (inherit-field rands)
    (define x (car rands))

    (define/override (update state)
      (cond
       [(send state get-stored this% x)
        => (lambda (n) (send (== (cadr rands) n) update state))]
       [else
        (let ([x (send state walk x)]
              [n (send state walk (cadr rands))])
          (cond
           [(and (list? x) (number? n))
            (or (and (= (length x) n) succeed) fail)]
           [(list? x)
            (send (== (length x) n) update state)]
           [(tree? x)
            (match-define (tree nodes) x)
            (define n* 
              (for/list ([node nodes]) (var (gensym 'n))))
            (send (apply conj 
                         (apply +@ (append n* (list n)))
                         (for/list ([node nodes] [n n*])
                           (length@ node n)))
                  update state)]
           [(number? n)
            (send (== (for/list ([i n]) (var (gensym 'i))) x)
                  update state)]
           [else (new this% [rands (list x n)])]))]))
    
    (define/public (get-value) (cadr rands))))

(define (length@ ls n) 
  (new length% [rands (list ls n)]))

