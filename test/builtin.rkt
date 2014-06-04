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

(require (except-in rackunit fail) 
         rackunit/text-ui racket/list
         racket/class racket/pretty)

(require "../main.rkt"
         "../src/testing.rkt")

(define (bar)
  (printf "====================================================\n"))

;; =============================================================================
;; tests

(define x (var 'x))
(define y (var 'y))
(define z (var 'z))

(define-dependency-test state-tests
  ()

  (check-true
   (equal? (new state%) (new state%)))

  (check-equal?
   (new state% [subst `((,x . 5))])
   (new state% [subst `((,x . 5))]))

  ;; add no new information to a satisfy state
  (check-equal?
   (send (new state% [subst `((,x . 5))])
         update (new state%))
   (new state% [subst `((,x . 5))]))

  (check-equal?
   (send (send (new state% [subst `((,x . 5))])
               update (new state% [subst `((,x . 5))]))
         trivial?)
   #t)

  (check-equal?
   (send (new state% [subst `((,x . ,y))])
         update (new state% [subst `((,y . 5))]))
   (new state% [subst `((,x . 5))]))

  (check-equal?
   (send (new state%) combine (new state% [subst `((,x . 5))]))
   (new state% [subst `((,x . 5))]))

  (define (foo x) (new base% [rands (list x)]))
  (check-false (send (new state%) has-stored (foo 5)))

  (check-equal?
   (send (new state% [store (list succeed)])
         update (new state%))
   (new state%))

  (check-equal?
   (send (new state%) update (new state% [subst `((,x . 5))]))
   (new state%))

  (check-equal?
   (send succeed run (new state%))
   (new state%))

  (check-false
   (send fail run (new state%)))

  (check-equal?
   (run succeed)
   (list (new state%)))

  (check-equal?
   (run fail)
   (list))

  (check-equal?
   (new state% [subst `((,x . 5) (,y . 6))])
   (new state% [subst `((,y . 6) (,x . 5))]))

  (check-equal?
   (new state% [subst `((,x . 5) (,y . 6) (,z . ,x))])
   (new state% [subst `((,y . 6) (,x . ,z) (,z . 5))])))

(define-dependency-test associate-tests
  (state-tests)

  (check-equal?
   (run (≡ x 5))
   (list (new state% [subst `((,x . 5))])))
  
  (check-equal?
   (run (≡ x #f))
   (list (new state% [subst `((,x . #f))])))
  
  (check-equal?
   (run (≡ x #f))
   (run (≡ #f x)))
  
  (check-equal?
   (run (≡ 5 x))
   (run (≡ x 5)))
  
  (check-equal?
   (run (≡ 5 (cons 1 2)))
   (run fail))

  (check-equal?
   (run (≡ (cons 1 2) 5))
   (run fail))

  (check-equal?
   (run (≡ x (cons 1 2)))
   (list (new state% [subst `((,x . ,(cons 1 2)))])))

  (check-equal?
   (run (≡ (cons 1 2) x))
   (run (≡ x (cons 1 2))))

  (check-run-succeed
   (≡ '() '()))

  (check-equal? 
   (run (≡ x '()))
   (list (new state% [subst `((,x . ()))]))))


(define-dependency-test conj-tests 
  (associate-tests)

  (check-equal?
   (run (conj (≡ x 5)))
   (run (≡ x 5)))
  
  (check-equal?
   (run (conj (conj (conj (conj (conj (≡ x 5)))))))
   (run (≡ x 5)))
  
  (check-equal?
   (run (conj (≡ x 5)
              (≡ x 5)))
   (run (conj (≡ x 5))))
  
  (check-equal?
   (run (≡ (cons 1 2) (cons 3 4)))
   (run fail))

  (check-equal?
   (run (≡ (list 1 2) (list 1 2)))
   (run (conj (≡ 1 1) (≡ 2 2))))

  (check-equal? (run (conj fail)) (run fail))

  (check-equal?
   (run (conj (≡ (cons (var 'a) (var 'd)) x)
              (≡ x (list 1 2 3))))
   (run (conj (≡ x (list 1 2 3))
              (≡ (var 'a) 1)
              (≡ (var 'd) (list 2 3)))))

  (check-equal?
   (take-a-inf
    #f
    (send (conj (== x 5) fail)
          augment (new state%)))
   (list)))

(define-dependency-test disj-tests
  (associate-tests conj-tests)

  (check-equal?
   (run (disj (≡ x 5)))
   (run (≡ x 5)))

  (check-equal? 
   (run (conj (disj (≡ x 5))
              (≡ x 5)))
   (run (≡ x 5)))
  
  (check-equal? 
   (run (conj (disj (≡ x 5) (≡ x 6))
              (≡ x 5)))
   (run (≡ x 5)))

  (check-equal?
   (run (exists (x y n)
          (conj (disj (conj (≡ n 0) (≡ x '()))
                      (conj (≡ n 1) (≡ x (list y))))
                (≡ n 1))))
   (run (exists (x y n)
          (conj (≡ n 1) (≡ x (list y))))))

  (check-equal?
   (run (disj (≡ x 1) (≡ x 2)))
   (append (run (≡ x 1)) (run (≡ x 2))))

  (check-equal?
   (query (f g)
          (conj (disj (≡ f 0) (≡ f 1))
                (disj (≡ g 0) (≡ g 1))))
   '((0 0) (1 0) (0 1) (1 1))
   ;; '((0 0) (0 1) (1 0) (1 1))
   )

  (check-equal?
   (disj (≡ x 5) (≡ x 6))
   (disj (≡ x 5) (≡ x 6)))

  (check-not-false
   (send (new state% [store (list (disj (≡ x 5) (≡ x 6)))])
         has-stored (disj (≡ x 5) (≡ x 6))))

  (check-equal?
   (run (conj (disj (≡ x 5) (≡ x 6))
              (disj (≡ x 5) (≡ x 6))))
   (run (disj (≡ x 5) (≡ x 6)))))

;; (define-dependency-test not-tests
;;   (associate-tests conj-tests disj-tests)
;;   
;;   (check-equal?
;;    (! (new state%)) 
;;    (! (new state%)))
;; 
;;   (check-equal?
;;    (send (! (conj (≡ x 5) (≡ y 6))) update (new state%))
;;    (send (disj (! (≡ y 6)) (! (≡ x 5))) update (new state%))))
;; 

(define-dependency-test project-tests
  (associate-tests conj-tests disj-tests)

  (check-quick-termination
   (send (disj (exists () (conj succeed (== x (list)))))
         augment (new state%)))

  (check-quick-termination
   (run (disj (exists () (conj (== x (list)) succeed)))))

  (check-quick-termination
   (run (project x [(list) succeed])))

  (check-equal?
   (run (project x [(list) succeed]))
   (run (== x (list))))

  (check-equal?
   (query (x)
     (project x [(cons a d) (conj (≡ a 5) (== (cdr x) 6))]))
   '((5 . 6)))

  (check-run-fail 
   (project x [(cons a d) fail]))

  (check-equal?
   (query (x) (project x [(list 1 2 3)]))
   '((1 2 3)))

  (check-equal?
   (query (x)
     (conj (project x [(tree (list y1 (list y) y2))])
           (== x (list 1 2 3))))
   '((1 2 3))))

(define-dependency-test operator-tests
  (associate-tests conj-tests disj-tests project-tests)

  (define foo@
    (lambda@ (x)
      (disj (== x (list)) (foo@ x))))

  ;; x is never a pair, so the conj should never be joined
  ;; if succeed triggers joining, this infinite loops
  (check-quick-termination (foo@ x))
  (check-quick-termination (run (foo@ x) 2))

  (check-equal?
   (query 2 (x) (foo@ x))
   '(())))

(define-dependency-test eigen-tests
  (operator-tests)

  (define e (eigen 'e))
  (let ([scope (list (list x) (list e) (list y))])
    (check-true  (check-scope? (list)   (list x) scope))
    (check-false (check-scope? (list e) (list x) scope))
    (check-true  (check-scope? (list e) (list y) scope))

    (check-equal?
     (send (new state%) associate e x scope)
     (new fail%))

    (check-equal?
     (send (new state%) associate e y scope)
     (new state% [subst `((,y . ,e))])))

  (check-equal? 
   (run (exists (x) (forall (e) (≡ e x))))
   (run fail))

  (check-one-answer
   (forall (e) (exists (y) (≡ e y))))

  (check-one-answer
   (conj (forall (e1) (exists (x1) (≡ e1 x1)))
         (forall (e2) (exists (x2) (≡ e2 x2)))))

  ;; scope: ((x) (e) (y))
  (check-equal?
   (run (exists (x) 
          (forall (e) 
            (exists (y) 
              (conj (≡ e y) (≡ x y))))))
   (run fail))

  (check-equal?
   (run (forall (e) (≡ e 5)))
   (run fail))

  (check-one-answer
   (forall (e) (exists (x) (≡ (list e) x))))

  (check-equal?
   (run (forall (e) (exists (x) (≡ (list x) e))))
   (run fail))

  (check-equal?
   (run (exists (x)
          (forall (e) 
            (exists (y)
              (conj (≡ (list e) y)
                    (≡ x y))))))
   (run fail))

  (check-equal?
   (run (exists (x)
          (forall (e)
            (exists (y)
              (conj (≡ (list y) x)
                    (≡ y e))))))
   (run fail))

  (check-equal?
   (run (exists (x)
          (forall (e)
            (exists (y)
              (conj (≡ y e)
                    (≡ (list y) x))))))
   (run (exists (x)
          (forall (e)
            (exists (y)
              (conj (≡ (list y) x)
                    (≡ y e)))))))

  (check-equal?
   (run (forall (e1 e2)
          (exists (x y)
            (conj (≡ x e1) (≡ y e2) (≡ x y)))))
   (run fail))

  (check-equal?
   (run (exists (x) 
          (forall (e) 
            (exists (y) 
              (≡ (cons e x) (cons x x))))))
   (run fail))

  (check-equal?
   (length (run (forall (x y)
                  (exists (z)
                    (disj (≡ z (cons x y))
                          (≡ z (cons y x)))))))
   2))

(define-dependency-test dom-tests
  (operator-tests)

  (check-equal?
   (run (dom@ x (range-dom 2 2)))
   (run (≡ x 2)))

  (check-equal?
   (run (conj (dom@ x (range-dom 1 2)) (dom@ x (range-dom 2 3))))
   (run (dom@ x (range-dom 2 2))))

  (check-equal? (length (run (dom@ x (range-dom 4 5)))) 2)

  (check-equal? 
   (run (conj (dom@ x (range-dom 1 10))
                     (dom@ x (range-dom 3 7))
                     (dom@ x (range-dom 4 5))))
   (run (dom@ x (range-dom 4 5))))

  (check-equal?
   (run (conj (conj (≡ x y)
                    (dom@ z (range-dom 1 2)))
              (conj (≡ y z)
                    (dom@ x (range-dom 2 3)))))
   (run (conj (≡ x y)
              (≡ y z)
              (≡ z 2))))

  (check-equal?
   (run (dom@ x (range-dom 0 1)))
   (run (disj (≡ x 0) (≡ x 1))))

  (check-false (send (new state%) get-stored dom% x))
  (check-false (send (new state%) get-stored dom% 5))

  (check-equal?
   (send (dom@ x (range-dom 0 1)) merge (number@ x) (new state%))
   (send (new state%) set-stored (dom@ x (range-dom 0 1))))

  (check-equal?
   (send (dom@ x (range-dom 0 1)) merge (symbol@ x) (new state%))
   (new fail%)))

(define-dependency-test fd-tests
  (operator-tests dom-tests)

  (check-equal?
   (run (+@ x 5 7))
   (run (≡ x 2)))

  (check-equal?
   (run (conj (dom@ x (range-dom 1 10))
              (+@ x 5 7)))
   (run (≡ x 2)))

  (check-equal?
   (run (conj (+@ x 5 7)
              (dom@ x (range-dom 1 10))))
   (run (conj (dom@ x (range-dom 1 10))
              (+@ x 5 7))))

  (check-equal?
   (run (exists (n1 n2) 
          (+@ n1 n2 1)))
   (run (exists (n1 n2)
          (disj (conj (≡ n2 1) (≡ n1 0))
                (conj (≡ n2 0) (≡ n1 1))))))

  (let ([c1 (+@ x y z)] [c2 (+@ z y x)])
    (check-false (send (send (new state%) set-stored c1)
                       has-stored c2))))

(define-dependency-test list-tests
  ()

  (check-run-succeed
   (list@ (list)))

  (check-run-succeed
   (list@ (list 1)))

  (check-run-succeed
   (list@ (list 1 2)))

  (check-equal?
   (run (list@ 4))
   (list))

  (check-equal?
   (run (list@ (cons 1 2)))
   (list))

  (check-equal?
   (run (list@ (cons 1 (cons 2 3))))
   (list)))

(define-dependency-test tree-tests
  (operator-tests list-tests)

  (check-equal?
   (list@ x)
   (tree@ x))

  (check-equal?
   (run (conj (list@ x) (tree@ x)))
   (run (list@ x)))

  (check-equal?
   (run (conj (list@ x) (tree@ x)))
   (run (conj (tree@ x) (list@ x))))

  (check-one-answer
   (== (list 5) (tree (list x))))

  (check-equal?
   (query (x) (== (list 5) (tree (list x (list 5) x))))
   '(()))

  (check-equal?
   (query (w x y z)
     (conj (== w (list y z))
           (== w (tree (list x x)))))
   '(((lv.0 lv.0) (lv.0) lv.0 lv.0))))

(define-dependency-test length-tests
  (operator-tests list-tests fd-tests tree-tests)
  
  (check-run-succeed
   (length@ (list 1 2 3) 3))

  (check-equal?
   (query 2 (x) (length@ (list 1 2 3) x))
   '(3))

  (let ([answer (run (exists (n1 n2)
                       (conj (length@ x n1) 
                             (length@ y n2)
                             (+@ n1 n2 1))))])
    (check-equal? (length answer) 2))

  (check-run-succeed
   (length@ (tree `()) 0))

  (check-one-answer
   (length@ (tree `((1 2))) 2))

  (check-one-answer
   (length@ (tree `((1) (2))) 2))

  (check-one-answer
   (length@ (tree `(() (1 2))) 2))

  (check-one-answer
   (length@ (tree `((1 2) ())) 2))

  (check-one-answer
   (conj (≡ x `(,y ,y)) (list@ `(,y ,y))))

  (check-one-answer
   (length@ (tree `(,x)) 2))

  (check-equal?
   (query 4 (x y) (length@ (tree `(,x ,y)) 1))
   '((() (lv.0)) ((lv.0) ())))

  (check-equal?
   (query (x y) (length@ (tree `(,x ,y)) 2))
   ;; '((() (lv.0 lv.1)) ((lv.0 lv.1) ()) ((lv.0) (lv.1)))
   '(((lv.0 lv.1) ()) (() (lv.0 lv.1)) ((lv.0) (lv.1)))
   )

  (check-run-fail
   (exists (x y) (length@ (tree `(,x (3) ,y)) 0)))

  (check-one-answer
   (exists (x y) (length@ (tree `(,x (3) ,y)) 1)))

  (check-equal?
   (length (run (exists (x y) (length@ (tree `(,x (3) ,y)) 2))))
   2)

  (check-equal?
   (query (x y)
          (exists (nx ny)
            (conj (length@ x nx)
                  (length@ y ny)
                  (+@ nx ny 0))))
   '((() ())))

  (check-equal?
   (query (x y)
          (exists (n nx ny)
            (conj (dom@ n (range-dom 0 1))
                  (length@ x nx)
                  (length@ y ny)
                  (+@ nx 1 ny n))))
   '((() ())))

  (check-equal?
   (query (x y)
          (exists (n)
            (conj (length@ (tree `(,x (3) ,y)) n)
                  (dom@ n (range-dom 0 1)))))
   '((() ())))

  (let ([answer (run (exists (n)
                       (conj (≡ z (tree `(,x (3) ,y)))
                             (length@ z n)
                             (dom@ n (range-dom 1 5)))))])
    (check-equal? (length answer) 15)))

(define-dependency-test list-of-tests
  (operator-tests list-tests tree-tests length-tests)

  (define (uw5 v) (≡ v 5))

  (check-equal?
   (query 1 (x) (list-of@ uw5 (list x)))
   '(5))

  (check-equal?
   (query 1 (x) (list-of@ (lambda (v) (≡ v 5)) (list x x x)))
   '(5))

  (check-equal?
   (query 2 (x) (list-of@ (lambda (v) (≡ v 5)) (list x x x)))
   '(5))

  (check-equal?
   (tree@ x)
   (list-of@ (lambda (v) succeed) x))

  (check-equal?
   (run (conj (tree@ x) (list-of@ (lambda (v) succeed) x)) 1)
   (run (list-of@ (lambda (v) succeed) x) 1))

  (check-equal? 
   (query (x) (conj (length@ x 3) (list-of@ (lambda (v) (≡ v 5)) x)))
   '((5 5 5)))

  (define@ (foo@ x thing)
    (project x
      [(tree (list y thing^ y))
       (conj (list-of@ uw5 y)
             (== thing^ thing))]))

  (check-equal?
   (query (z) 
     (exists (n1 n2)
       (conj (== z (tree (list y (list) y)))
             (length@ y n1)
             (length@ y n2)
             (+@ n1 n2 1))))
   '())

  (check-equal?
   (query (z) 
     (conj (== z (tree (list y y)))
           (length@ z 1)))
   '())

  (check-equal?
   (run (conj (foo@ z (list)) (length@ z 1)))
   '())

  (check-equal?
   (query (z) 
     (conj (== z (tree (list y (list 5) y)))
           (length@ z 1)))
   `(,(tree (list (list) (list 5) (list)))))

  (check-equal?
   (query (z) 
     (conj (foo@ z (list 5))
           (length@ z 1)))
   '((5))))

(define-dependency-test ground-attribute-tests
  (operator-tests)

  (check-run-succeed (symbol@ 'x))
  (check-run-fail (symbol@ 5))

  (check-run-fail (number@ 'x))
  (check-run-succeed (number@ 5))

  (check-run-fail
   (conj (symbol@ x) (number@ x))))

(define-dependency-test stlc-tests
  (operator-tests list-of-tests eigen-tests)

  (define@ (lookup@ gamma x t)
    (project gamma
      [(cons a d)
       (disj
        (≡ a `(,x . ,t))
        (exists (y s)
          (conj (≡ a `(,y . ,s))
                (lookup@ d x t))))]))
  
  (check-run-succeed
   (lookup@ `((x . int)) `x `int))

  (check-equal?
   (run (lookup@ `((x . int)) x `int))
   (run (≡ x 'x)))

  (check-run-fail
   (lookup@ `() x `int))

  (check-run-fail
   (lookup@ `((x . bool)) `x `int))

  (check-quick-termination
   (query (x) (lookup@ `((x1 . int) (x2 . int)) x `int)))

  (check-equal?
   (query (x) (lookup@ `((x1 . int) (x2 . int)) x `int))
   '(x1 x2))

  (define@ (⊢@ gamma expr type)
    (project expr
      [`(num ,x)
       (≡ type `int)]
      [`(bool ,b) 
       (≡ type `bool)]
      [`(var ,x)
       (lookup@ gamma x type)]
      [`(lambda (,x) ,body)
       (exists (t1 t2)
         (conj (≡ type `(-> ,t1 ,t2))
               (⊢@ `((,x . ,t1) . ,gamma) body t2)))]
      [`(app ,fn ,arg)
       (exists (t1)
         (conj (⊢@ gamma fn `(-> ,t1 ,type))
               (⊢@ gamma arg t1)))]))
  
  (check-run-fail
   (⊢@ `() `(var x) `int))
  
  (check-run-succeed
   (⊢@ `((x . int)) `(var x) `int))

  (check-equal?
   (run (⊢@ `((x . int)) `(var ,x) `int))
   (run (≡ x `x)))

  (check-run-succeed
   (⊢@ `() `(num 5) `int))

  (check-one-answer
   (⊢@ `() `(lambda (x) (var x)) `(-> int int)))

  (check-one-answer
   (exists (body)
     (conj (== body `(var x))
           (⊢@ `() `(lambda (x) ,body) `(-> int int)))))

  (check-one-answer
   (exists (fn)
     (conj (== fn `(lambda (x) (var x)))
           (⊢@ `() fn `(-> int int)))))

  (check-one-answer
   (⊢@ `() `(app (lambda (x) (var x)) (num 5)) `int))

  (check-quick-termination
   (run (⊢@ `() x `int) 1))

  (check-long-termination
   (query 2 (x) (⊢@ `() x `int)))

  (check-equal?
   (query 2 (x) (⊢@ `() `(lambda (x) ,x) `(-> int int)))
   '((num lv.0) (var x)))

  (check-long-termination
   (query 3 (x) (⊢@ `() `(lambda (x) ,x) `(-> int int))))

  (check-equal?
   (query 3 (x) (⊢@ `() `(lambda (x) ,x) `(-> int int)))
   '((num lv.0) (var x) (app (lambda (lv.0) (num lv.1)) (num lv.2))))

  (check-long-termination
   (query 5 (x) (⊢@ `() `(lambda (x) ,x) `(-> int int))))

  (check-run-succeed
   (forall (e) (⊢@ `() `(num ,e) `int)))

  (check-equal?
   (query (x) (⊢@ `((x . int)) `(lambda (,x) (var x)) `(-> int int)))
   '(x lv.0))
  
  (check-equal?
   (query (stuff) (⊢@ `((x . int)) `(lambda ,stuff (var x)) `(-> int int)))
   '((x) (lv.0))))

(define-dependency-test dd-tests
  (operator-tests)
  
  (define (string@ x)
    (new (ground-type-mixin string?) [rands (list x)]))

  (define@ (dd-term x)
    (disj (c-term x)
          (p-term x)
          (r-term x)
          (e-term x)
          (d-term x)
          (items-term x)
          (named-term x)
          (x-term x)))

  (define@ (c-term x)
    (project x
      [`(configuration ,p ,rs)
       (conj (p-term p) (list-of@ r-term rs))]))

  (define@ (p-term x)
    (project x
      [`(player ,named ,y)
       (conj (named-term named) (x-term y))]))

  (define@ (r-term x)
    (project x
      [`(room ,y ,items ,e)
       (conj (x-term y) 
             (items-term items)
             (e-term e))]))

  (define@ (e-term x)
    (list-of@ (lambda (thing)
               (project thing
                 [`(,d ,x)
                  (conj (d-term d)
                        (x-term x))]))
             x))

  (define@ (d-term x)
    (project x
      [`north]
      [`east]
      [`south]
      [`west]))

  (define@ (items-term x) (string@ x))
  (define@ (named-term x) (string@ x))
  (define@ (x-term x) (symbol@ x))

  (define-syntax-rule (term x) (quasiquote x))

  (define c0
    (term 
     [configuration 
      (player "matthias" living)
      ((room living "green" ((east sitting)))
       (room sitting "blue" ((east dining) (west living)))
       (room dining "red" ((west sitting))))]))

  (define c0-extended
    (term 
     [configuration 
      (player "matthias" living)
      ((room living "green" ((east sitting)))
       (room sitting "blue" ((east dining) (west living) (south kitchen)))
       (room dining "red" ((west sitting) (north kitchen)))
       (room kitchen "yellow" ((south dining) (north sitting))))]))

  (define c1
    (term 
     [configuration 
      (player "matthias" living)
      [(room living "green" ((east sitting)))
       (room sitting "blue" ((west living) (east dining)))
       (room dining "red" ((west sitting)))]]))

  (define c2 
    (term 
     [configuration 
      (player "matthias" sitting)
      [(room living "green" ((east sitting)))
       (room sitting "blue" ((west living) (east dining)))
       (room dining "red" ((west sitting)))]]))

  (define c3
    (term 
     [configuration 
      (player "matthias" dining)
      [(room living "green" ((east sitting)))
       (room sitting "blue" ((west living) (east dining)))
       (room dining "red" ((west sitting)))]]))

  (define c1-alt
    (term 
     [configuration 
      (player "matthias" living)
      [(room sitting "blue" ((west living) (east dining)))
       (room living "green" ((east sitting)))
       (room dining "red" ((west sitting)))]]))

  (define c2-alt
    (term 
     [configuration 
      (player "matthias" sitting)
      [(room sitting "blue" ((west living) (east dining)))
       (room living "green" ((east sitting)))
       (room dining "red" ((west sitting)))]]))

  (define-syntax-rule (tt c)
    (check-one-answer (c-term c)))

  (tt c0)
  (tt c1)
  (tt c2)
  (tt c3)
  (tt c1-alt)
  (tt c2-alt)

  (define@ (d-opposite d1 d2)
    (disj
     (conj (== d1 'south) (== d2 'north))
     (conj (== d1 'north) (== d2 'south))
     (conj (== d1 'east)  (== d2 'west))
     (conj (== d1 'west)  (== d2 'east))))

  (define@ (wf-connections gamma d x y)
    (project gamma
      [(tree (list r1 (list r) r2))
       (exists (x items e)
         (conj (list-of@ r-term r1)
               (list-of@ r-term r2)
               (== r `(room ,x ,items ,e))
               (project e
                 [(tree (list dx1 (list (list do xf)) dx2))
                  (conj (== y xf) (d-opposite do d))])))]))
  
  (define rooms1 (term ,(third c1)))
  (define room1-rooms1 (first rooms1))
  (define exits-room1-rooms1 (first (fourth (first rooms1))))

  (check-one-answer
   (wf-connections 
    rooms1 
    (first exits-room1-rooms1)
    (second exits-room1-rooms1)
    (second room1-rooms1)))

  (define@ (wf-exits-proper gamma e y)
    (list-of@ (lambda (dx)
                (project dx
                  [(list d x)
                   (wf-connections gamma d x y)]))
              e))

  ;; (check-one-answer
  ;;  (wf-exits-proper rooms1 (fourth (first rooms1)) (second (first rooms1))))
  ;; (check-one-answer
  ;;  (wf-exits-proper rooms1 (fourth (second rooms1)) (second (second rooms1))))
  ;; (check-one-answer
  ;;  (wf-exits-proper rooms1 (fourth (third rooms1)) (second (third rooms1))))

  )

(define builtin-test-suite
  (test-suite 
   "builtin tests"
   
   (time (state-tests))
   (time (associate-tests))
   (time (conj-tests))
   (time (disj-tests))
   (time (project-tests))
   (time (operator-tests))

   (time (eigen-tests))
   (time (list-tests))
   (time (ground-attribute-tests))
   (time (dom-tests))
   (time (fd-tests))
   (time (tree-tests))
   (time (length-tests))
   (time (list-of-tests))

   (time (stlc-tests))
   (time (dd-tests))))

(module+ test
  (parameterize ([pretty-print-columns 102]
                 [print-reader-abbreviations #t])
    (time (void (run-tests builtin-test-suite)))))

(module+ main
  (require (submod ".." test)))
