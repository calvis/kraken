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

(require (except-in rackunit fail) rackunit/text-ui racket/format
         racket/class racket/pretty)
(require (for-syntax racket/base syntax/parse))
(require "../main.rkt")

(define (bar)
  (printf "====================================================\n"))

;; =============================================================================
;; testing facilities

(provide check-quick-termination
         check-long-termination
         check-one-answer
         check-run-succeed
         check-run-fail)

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
  (check-termination-macro 50 expr))
(define-syntax-rule (check-long-termination expr)
  (check-termination-macro 10000 expr))

(define-simple-check (check-one-answer expr)
  (= 1 (length (run expr 2))))

(define-simple-check (check-run-succeed expr)
  (equal? (run expr) (run succeed)))

(define-simple-check (check-run-fail expr)
  (equal? (run expr) (run fail)))

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

  (check-equal?
   (run succeed)
   (list (new state%)))

  (define (foo x) (new base% [rands (list x)]))
  (check-false (send (new state%) has-stored (foo 5)))

  (check-equal?
   (send (new state% [store (list succeed)])
         update (new state%))
   (new state%))

  (check-equal?
   (send (new state%) update (new state% [subst `((,x . 5))]))
   (new state%)))

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
   (list (new state% [subst `((,x . ()))])))

  (check-equal?
   (send (new state% [store (list (≡ (cdr@ (list 1)) (list)))])
         update (new state%))
   (new state%)))

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
              (≡ (var 'd) (list 2 3))))))

(define-dependency-test disj-tests
  (associate-tests)

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
   '((0 0) (1 0) (0 1) (1 1))))

(require racket/engine)

(define-dependency-test shape-tests
  (conj-tests)

  (check-equal?
   (send (shape (cons 1 2) (cons (any) (any)))
         update (new state%))
   (new state%)))

(define-dependency-test ==>-tests
  (shape-tests)

  (let ([c (==> (shape 4 (list)))])
    (check-not-false
     (send (new state% [store (list c)]) has-stored c)))

  (check-equal?
   (send (new state% [store (list (==> (shape 4 (list))))])
         update (new state%))
   (new fail%))

  (check-equal?
   (send (new state% [store (list (==> (≡ x 5)))])
         associate x 5)
   (new state% [subst `((,x . 5))]))

  (check-equal?
   (send (new ==>%
              [test (send (new state%) associate x 5)]
              [consequent succeed])
         update (send (new state%) associate x 5))
   (new state%))

  (check-equal?
   (==> (≡ x 5))
   (new ==>% 
        [test (new state% [subst `((,x . 5))])]
        [consequent succeed]))

  (check-equal?
   (send (new state% [store (list (==> (≡ x 5)))])
         update (new state% [subst `((,x . 5))]))
   (new state%))

  (check-equal?
   (==> (==> (≡ x 5)))
   (new ==>%
        [test (new state% [store (list (==> (≡ x 5)))])]
        [consequent succeed]))

  (check-equal?
   (send (new state% [store (list (==> (==> (≡ x 5))))])
         update (new state% [subst `((,x . 5))]))
   (new state%))

  (check-equal?
   (send (send (==> (==> (≡ x 5)))
               combine (new state%))
         update (new state% [subst `((,x . 5))]))
   (new state%))

  (check-equal?
   (query (z)
          (conj (==> (==> (≡ x 5))
                     (≡ z 5))
                (≡ x 5)))
   '(5))

  (check-equal?
   (query (z)
          (conj (==> (conj (==> (≡ x 5)
                                (≡ y 6))
                           (≡ y 6))
                     (≡ z 5))
                (≡ x 5) (≡ y 6)))
   '(5)))

(define-dependency-test operator-tests
  (associate-tests conj-tests disj-tests shape-tests ==>-tests)

  (define@ (foo x)
    (==> (shape x (cons (any) (any)))
         (conj succeed (foo (cdr@ x)))))

  ;; x is never a pair, so the conj should never be joined
  ;; if succeed triggers joining, this infinite loops
  (check-quick-termination (foo x)))

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
  (check-false (send (new state%) get-stored dom% 5)))

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
   (list)))

(define-dependency-test tree-tests
  (operator-tests list-tests)

  (check-equal?
   (list@ x)
   (tree/a x))

  (check-equal?
   (run (conj (list@ x) (tree/a x)))
   (run (list@ x)))

  (check-equal?
   (run (conj (list@ x) (tree/a x)))
   (run (conj (tree/a x) (list@ x)))))

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
   '((() (_.0)) ((_.0) ())))

  (check-equal?
   (query (x y) (length@ (tree `(,x ,y)) 2))
   '((() (_.0 _.1)) ((_.0) (_.1)) ((_.0 _.1) ())))

  (let ([n1 (var 'n1)]
        [n2 (var 'n2)]
        [n3 (var 'n3)]
        [n^ (var 'n^)])
    (let ([n* (list n1 n2 n3)])
      (check-equal?
       (send (conj 
              (apply +@ (append n* (list 1)))
              (length@ x n1)
              (length@ (list 3) n2)
              (length@ y n3))
             update (new state%))
       (new state% [subst `((,n2 . 1)
                           (,n1 . 0)
                           (,n^ . 1)
                           (,n3 . 0)
                           (,x . ())
                           (,y . ()))]))))

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

(define-dependency-test dots-tests
  (operator-tests list-tests tree-tests length-tests)

  (define (uw5 v) (≡ v 5))

  (check-equal?
   (send (disj (==> (shape (list x) (list)))
               (==> (shape (list x) (cons (any) (any)))
                    (conj (≡ x 5) (dots@ uw5 (cdr@ (list x))))))
         update (new state%))
   (new state% [subst `((,x . 5))]))

  (check-equal?
   (query 1 (x) (dots@ uw5 (list x)))
   '(5))

  (check-equal?
   (query 1 (x) (dots@ (lambda (v) (≡ v 5)) (list x x x)))
   '(5))

  (check-equal?
   (query 2 (x) (dots@ (lambda (v) (≡ v 5)) (list x x x)))
   '(5))

  (check-equal?
   (tree/a x)
   (dots@ (lambda (v) succeed) x))

  (check-equal?
   (run (conj (tree/a x) (dots@ (lambda (v) succeed) x)) 1)
   (run (dots@ (lambda (v) succeed) x) 1))

  (check-equal? 
   (query (x) (conj (length@ x 3) (dots@ (lambda (v) (≡ v 5)) x)))
   '((5 5 5))))

(define-dependency-test stlc-tests
  (operator-tests dots-tests)

  (define (symbol/a x)
    (define symbol%
      (class unary-attribute%
        (super-new)
        (inherit-field rands)
        
        (define/augment (update state)
          (let ([x (send state walk (car rands))])
            (cond
             [(symbol? x) succeed]
             [(var? x) (new this% [rands (list x)])]
             [else fail])))))
    (new symbol% [rands (list x)]))

  (check-run-succeed (symbol/a 'x))
  (check-run-fail (symbol/a 5))

  (define@ (lookup@ gamma x t)
    (==> (shape gamma (cons (any) (any)))
         (disj
          (≡ (car@ gamma) `(,x . ,t))
          (fresh (y s)
            (conj (≡ (car@ gamma) `(,y . ,s))
                  (lookup@ (cdr@ gamma) x t))))))
  
  (check-one-answer
   (≡ (car@ `((x . int))) (cons `x `int)))

  (check-one-answer
   (==> (shape `((x . int)) (cons (any) (any)))
        (≡ (car@ `((x . int))) (cons `x `int))))

  (check-one-answer
   (==> (shape `((x . int)) (cons (any) (any)))
        (disj (≡ `(x . int) `(x . int)) (lookup@ `() `x `int))))
  
  (check-run-succeed
   (lookup@ `((x . int)) `x `int))

  (check-equal?
   (run (lookup@ `((x . int)) x `int))
   (run (≡ x 'x)))

  (check-run-fail
   (lookup@ `() x `int))

  (check-run-fail
   (lookup@ `((x . bool)) `x `int))

  (define@ (⊢@ gamma expr type)
    (case-shape expr
      [(num ,(any)) (≡ type `int)]
      [(var ,(any)) (lookup@ gamma (car@ (cdr@ expr)) type)]
      [(lambda (,(any)) ,(any))
       (fresh (x body t1 t2)
         (conj (≡ expr `(lambda (,x) ,body))
               (≡ type `(-> ,t1 ,t2))
               (⊢@ `((,x . ,t1) . ,gamma) body t2)))]
      [(app ,(any) ,(any))
       (fresh (fn arg t1)
         (conj (≡ expr `(app ,fn ,arg))
               (⊢@ gamma fn `(-> ,t1 ,type))
               (⊢@ gamma arg t1)))]))
  
  (check-run-fail
   (==> (shape `(num 5) `(var ,x)) succeed))

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
   (==> (shape `(app (lambda (x) (var x)) (num 5)) `(app ,(any) ,(any)))
        (conj (⊢@ `() `(lambda (x) (var x)) `(-> int int))
              (⊢@ `() `(num 5) `int))))

  (check-one-answer
   (==> (shape `(app (lambda (x) (var x)) (num 5)) `(app ,(any) ,(any)))
        (fresh (t1)
          (conj (⊢@ `() `(lambda (x) (var x)) `(-> ,t1 int))
                (⊢@ `() `(num 5) t1)))))

  (check-one-answer
   (fresh (body)
     (conj (== body `(var x))
           (⊢@ `() `(lambda (x) ,body) `(-> int int)))))

  (check-one-answer
   (fresh (fn)
     (conj (== fn `(lambda (x) (var x)))
           (⊢@ `() fn `(-> int int)))))

  (check-one-answer
   (fresh (expr type gamma)
     (conj
      (≡ expr `(lambda (x) (var x)))
      (≡ type `(-> int int))
      (≡ gamma `())
      (==> (shape expr `(lambda (,(any)) ,(any)))
           (fresh (x body t1 t2)
             (conj (≡ expr `(lambda (,x) ,body))
                   (≡ type `(-> ,t1 ,t2))
                   (⊢@ `((,x . ,t1) . ,gamma) body t2)))))))

  (check-one-answer
   (⊢@ `() `(app (lambda (x) (var x)) (num 5)) `int)))

(define builtin-test-suite
  (test-suite 
   "builtin tests"
   
   (time (state-tests))
   (time (associate-tests))
   (time (conj-tests))
   (time (disj-tests))
   (time (shape-tests))
   (time (==>-tests))
   (time (operator-tests))

   (time (eigen-tests))
   (time (list-tests))
   (time (dom-tests))
   (time (fd-tests))
   (time (tree-tests))
   (time (length-tests))
   (time (dots-tests))

   (time (stlc-tests))))

(module+ test
  (parameterize ([pretty-print-columns 102])
    (time (void (run-tests builtin-test-suite)))))

(module+ main
  (require (submod ".." test)))
