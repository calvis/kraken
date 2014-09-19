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
;; symbol@

(define symbol% (ground-type-mixin symbol?))
(define (symbol@ x) (new symbol% [rands (list x)]))

;; -----------------------------------------------------------------------------
;; list@

;; todo: list has an interpretation, but you should still be able to
;; quickly get/set it as an attribute?  and it shouldn't infinite loop
;; the projection (bc reifiable)

(define list%
  (class tree%
    (super-new)
    (define/override (get-sexp-rator) 'list@)
    (define/public (body ls)
      (project ls [(list)] [(cons a d) (list@ d)]))))

(define (list@ ls)
  (new (partial-attribute-mixin list%) [rands (list ls)]))

;; -----------------------------------------------------------------------------
;; list-of@

(define list-of%
  (class list%
    (super-new)
    (define/override (get-sexp-rator) 'list-of@)
    (define/override (body ls fn)
      (project ls
        [(list)]
        [(cons a d) (conj (fn a) (list-of@ fn d))]))))

(define (list-of@ fn ls)
  (new (partial-attribute-mixin list-of%) [rands (list ls fn)]))

;; -----------------------------------------------------------------------------
;; length@

(define length%
  (class tree%
    (super-new)
    (inherit-field rands)
    (define x (car rands))

    (define/override (update state)
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
         [else (new this% [rands (list x n)])])))

    (define/augment (merge attr^ state)
      (send
       (send (== (cadr rands) (send attr^ get-value)) update state)
       combine state))
    
    (define/public (get-value) (cadr rands))))

(define (length@ ls n) 
  (new length% [rands (list ls n)]))

