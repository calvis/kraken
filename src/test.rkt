#lang racket

(require (except-in rackunit fail) rackunit/text-ui)
(require (for-syntax racket/base syntax/parse))
(require "main.rkt")

;; =============================================================================
;; testing facilities

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

;; =============================================================================
;; tests

(define x (var 'x))
(define y (var 'y))
(define z (var 'z))

(define-dependency-test state-tests
  ()

  (check-equal?
   (new join% [s `((,x . 5))])
   (new join% [s `((,x . 5))]))

  (check-equal?
   (run succeed)
   (list empty-state)))

(define-dependency-test associate-tests
  (state-tests)

  (check-equal?
   (run (≡ x 5))
   (list (new join% [s `((,x . 5))])))
  
  (check-equal?
   (run (≡ x #f))
   (list (new join% [s `((,x . #f))])))
  
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
   (list (new join% [s `((,x . ,(cons 1 2)))])))

  (check-equal?
   (run (≡ (cons 1 2) x))
   (run (≡ x (cons 1 2))))

  (check-equal?
   (run (≡ '() '()))
   (list empty-state))

  (check-equal? 
   (run (≡ x '()))
   (list (new join% [s `((,x . ()))]))))

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

  (let ([state (run (conj (≡ (cons (var 'a) (var 'd)) x)
                          (≡ x (list 1 2 3))))])
    (check-not-false state)))

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
   (run (conj (disj (≡ x 5)
                    (≡ x 6))
              (≡ x 5)))
   (run (≡ x 5)))

  (define n (var 'n))

  (check-equal?
   (run (conj (disj (conj (≡ n 0)
                          (≡ x '()))
                    (conj (≡ n 1)
                          (≡ x (list y))))
              (≡ n 1)))
   (run (conj (≡ n 1)
              (≡ x (list y)))))

  (check-equal?
   (run (disj (≡ x 1) (≡ x 2)))
   (list (send empty-state associate x 1)
         (send empty-state associate x 2)))

  (check-equal?
   (map
    (lambda (state) (send state reify (list x y)))
    (run (conj (disj (≡ x 0) (≡ x 1))
               (disj (≡ y 0) (≡ y 1)))))
   '((0 0)
     (1 0)
     (0 1)
     (1 1))))

(require racket/engine)

(define-dependency-test shape-tests
  ())

(define-dependency-test ==>-tests
  ())

(define-dependency-test operator-tests
  (associate-tests conj-tests disj-tests ==>-tests shape-tests)

  (define-constraint (foo x)
    (==> (shape x (cons (any) (any)))
         (conj succeed (foo (cdr/o x)))))

  ;; x is never a pair, so the conj should never be joined
  ;; if succeed triggers joining, this infinite loops
  (check-quick-termination (foo x)))

(define-dependency-test map-tests
  (operator-tests)

  (check-equal? 
   (run (map/o ≡ (list x) (list y)))
   (run (≡ x y))))

(define-dependency-test dom-tests
  (operator-tests)

  (check-equal?
   (run (dom/a x (range-dom 2 2)))
   (run (≡ x 2)))

  (check-equal?
   (run (conj (dom/a x (range-dom 1 2)) (dom/a x (range-dom 2 3))))
   (run (dom/a x (range-dom 2 2))))

  (let ([answer (run (dom/a x (range-dom 4 5)))])
    (check-equal? (length answer) 2 (~a answer)))

  (let ([state (conj (dom/a x (range-dom 1 10))
                     (dom/a x (range-dom 3 7))
                     (dom/a x (range-dom 4 5)))])
    (check-equal? (run state) (run (dom/a x (range-dom 4 5)))))

  (check-equal?
   (run (conj (conj (≡ x y)
                    (dom/a z (range-dom 1 2)))
              (conj (≡ y z)
                    (dom/a x (range-dom 2 3)))))
   (run (conj (≡ x y)
              (≡ y z)
              (≡ z 2)))))

(define-dependency-test fd-tests
  (operator-tests dom-tests)

  (check-equal?
   (run (+/o x 5 7))
   (run (≡ x 2)))

  (check-equal?
   (run (conj (dom/a x (range-dom 1 10))
              (+/o x 5 7)))
   (run (≡ x 2)))

  (check-equal?
   (run (conj (+/o x 5 7)
              (dom/a x (range-dom 1 10))))
   (run (conj (dom/a x (range-dom 1 10))
              (+/o x 5 7)))))

(define-dependency-test list-tests
  ()
  
  (let ([answer (run (cdr/o x '()))])
    (check-false (null? answer)))

  (check-equal?
   (run (list/a (list)))
   (list empty-state))

  (check-equal?
   (run (list/a (list 1)))
   (list empty-state))

  (check-equal?
   (run (list/a (list 1 2 3)))
   (list empty-state))

  (check-equal?
   (run (list/a 4))
   (list)))

(define-dependency-test length-tests
  (operator-tests list-tests fd-tests)
  
  (check-equal?
   (run (length/a (list 1 2 3) 3))
   (list empty-state))

  (let ([state (send (length/a (list 1 2 3) x) join empty-state)])
    (check-not-false state)
    (let ([answer (send state narrow)])
      (check-false (null? answer) (~a answer))
      (check-true (null? (cdr answer)) (~a answer))

      (check-equal? (send (car answer) walk x) 3
                    (~a (car answer)))))

  (let ([answer (run (length/a x 3) 2)])
    (check-false (null? answer))
    (check-true (null? (cdr answer)) (~a answer))

    (check-equal? (length (send (car answer) walk x)) 3 (~a (car answer))))

  (define n1 (var 'n1)) (define n2 (var 'n2))
  (let ([state (send (conj (length/a x n1) (length/a y n2) (+/o n1 n2 1)) join (new join%))])
    (check-not-false state)
    (let ([answer (send state narrow 3)])
      (check-false (null? answer))
      (check-equal? (length answer) 2 (~a answer)))))

(define-dependency-test tree-tests
  (operator-tests length-tests list-tests)

  (check-equal?
   (run (conj (list/a x) (tree/a x)))
   (run (list/a x)))

  (check-equal?
   (run (conj (list/a x) (tree/a x)))
   (run (conj (tree/a x) (list/a x))))

  (let ([answer (run (length/a (tree `()) 0))])
    (check-false (null? answer)))

  (let ([answer (run (length/a (tree `((1 2))) 2))])
    (check-false (null? answer)))

  (let ([answer (run (length/a (tree `((1) (2))) 2))])
    (check-false (null? answer)))

  (let ([answer (run (length/a (tree `(() (1 2))) 2))])
    (check-false (null? answer)))

  (let ([answer (run (length/a (tree `((1 2) ())) 2))])
    (check-false (null? answer)))

  (let ([answer (run (conj (≡ x `(,y ,y)) (list/a `(,y ,y))))])
    (check-false (null? answer)))

  (let ([answer (run (length/a (tree `(,x)) 2))])
    (check-false (null? answer)))

  (let ([state (send (length/a (tree `(,x ,y)) 2) join empty-state)])
    (check-not-false state)

    (let ([answer (send state narrow 4)])
      (check-false (null? answer))
      (check-true (is-a? (car answer) state%) (~a (car answer)))

      (check-equal?
       (map (lambda (state) (send state reify (list x y))) answer)
       '((() (_.0 _.1)) ((_.0) (_.1)) ((_.0 _.1) ())))))

  (let ([answer (run (length/a (tree `(,x (3) ,y)) 3))])
    (check-false (null? answer))
    (check-equal? (length answer) 3))

  (define n (var 'n))
  (let ([answer (run (conj (≡ z (tree `(,x (3) ,y)))
                           (length/a z n)
                           (dom/a n (range-dom 1 5))))])
    (check-false (null? answer))
    (check-equal? (length answer) 15)))

(define-dependency-test dots-tests
  (operator-tests list-tests tree-tests)

  (check-equal?
   (map (lambda (state) (send state reify x))
        (run (dots/a (lambda (v) (≡ v 5)) (list x x x)) 1))
   '(5))

  (check-equal?
   (run (conj (tree/a x) (dots/a (lambda (v) succeed) x)) 1)
   (run (dots/a (lambda (v) succeed) x) 1))
  
  (check-equal?
   (send (send (dots/a (lambda (v) succeed) x) join (new join%))
         set-attribute (tree/a x))
   (send (dots/a (lambda (v) succeed) x) join (new join%)))
  
  (let ([state (conj (length/a x 3) (dots/a (lambda (v) (≡ v 5)) x))])
    (let ([answer (run state)])
      (check-false (null? answer))
      (check-equal? (map (lambda (state) (send state reify x)) answer) 
                    '((5 5 5))))))

(define-dependency-test stlc-tests
  (operator-tests dots-tests)

  (define (symbol/a x)
    (define symbol%
      (class unary-attribute%
        (super-new)
        (inherit-field rands)
        
        (define/augment (join state)
          (let ([x (send state walk (car rands))])
            (cond
             [(symbol? x)
              state]
             [(var? x)
              (send state set-attribute (new this% [rands (list x)]))]
             [else fail])))
        
        (define/augride (satisfy state)
          (let ([x (send state walk (car rands))])
            (or (symbol? x) (and (var? x) (symbol/a x)))))))
    (new symbol% [rands (list x)]))

  (check-equal? (run (symbol/a 'x)) (list empty-state))
  (check-equal? (run (symbol/a 5))  (list))

  (define-constraint (lookup/o gamma x t)
    (==> (shape gamma (cons (any) (any)))
         (disj
          (≡ (car/o gamma) `(,x . ,t))
          (fresh (y s)
            (conj (≡ (car/o gamma) `(,y . ,s))
                  (lookup/o (cdr/o gamma) x t))))))
  
  (check-equal?
   (run (≡ (car/o `((x . int))) (cons `x `int)))
   (list empty-state))

  (check-equal?
   (run (==> (shape `((x . int)) (cons (any) (any)))
             (≡ (car/o `((x . int))) (cons `x `int))))
   (list empty-state))

  (check-equal?
   (run (==> (shape `((x . int)) (cons (any) (any)))
             (disj (≡ `(x . int) `(x . int)) (lookup/o `() `x `int))))
   (list empty-state))
  
  (check-equal?
   (run (lookup/o `((x . int)) `x `int))
   (list (new join%)))

  (check-equal?
   (run (lookup/o `((x . int)) x `int))
   (run (≡ x 'x)))

  (check-equal?
   (run (lookup/o `() x `int))
   (run fail))

  (check-equal?
   (run (lookup/o `((x . bool)) `x `int))
   (run fail))

  (define-constraint (⊢/o gamma expr type)
    (case-shape expr
      [(num ,(any)) (≡ type `int)]
      [(var ,(any)) (lookup/o gamma (car/o (cdr/o expr)) type)]
      [(lambda (,(any)) ,(any))
       (fresh (x body t1 t2)
         (conj (≡ expr `(lambda (,x) ,body))
               (≡ type `(-> ,t1 ,t2))
               (⊢/o `((,x . ,t1) . ,gamma) body t2)))]
      [(app ,(any) ,(any))
       (fresh (fn arg t1)
         (conj (≡ expr `(app ,fn ,arg))
               (⊢/o gamma fn `(-> ,t1 ,type))
               (⊢/o gamma arg t1)))]))
  
  (check-equal?
   (run (==> (shape `(num 5) `(var ,x)) succeed))
   (run fail))

  (check-equal?
   (run (⊢/o `() `(var x) `int))
   (run fail))
  
  (check-equal?
   (run (⊢/o `((x . int)) `(var x) `int))
   (run succeed))

  (check-equal?
   (run (⊢/o `((x . int)) `(var ,x) `int))
   (run (≡ x `x)))

  (check-equal?
   (run (⊢/o `() `(num 5) `int))
   (run succeed))

  (check-true
   (= (length (run (⊢/o `() `(lambda (x) (var x)) `(-> int int)))) 1))

  (check-equal?
   (length
    (run (==> (shape `(app (lambda (x) (var x)) (num 5)) `(app ,(any) ,(any)))
              (conj (⊢/o `() `(lambda (x) (var x)) `(-> int int))
                    (⊢/o `() `(num 5) `int)))))
   1)

  (check-equal?
   (length
    (run (==> (shape `(app (lambda (x) (var x)) (num 5)) `(app ,(any) ,(any)))
              (fresh (t1)
                (conj (⊢/o `() `(lambda (x) (var x)) `(-> ,t1 int))
                      (⊢/o `() `(num 5) t1))))))
   1)

  (check-equal?
   (length
    (run (fresh (body)
           (conj (== body `(var x))
                 (⊢/o `() `(lambda (x) ,body) `(-> int int))))))
   1)

  (check-equal?
   (length
    (run (fresh (fn)
           (conj (== fn `(lambda (x) (var x)))
                 (⊢/o `() fn `(-> int int))))))
   1)

  (check-equal?
   (length
    (run (fresh (expr type gamma)
           (conj
            (≡ expr `(lambda (x) (var x)))
            (≡ type `(-> int int))
            (≡ gamma `())
            (==> (shape expr `(lambda (,(any)) ,(any)))
                 (fresh (x body t1 t2)
                   (conj (≡ expr `(lambda (,x) ,body))
                         (≡ type `(-> ,t1 ,t2))
                         (⊢/o `((,x . ,t1) . ,gamma) body t2))))))))
   1)

  (check-equal?
   (length (run (⊢/o `() `(app (lambda (x) (var x)) (num 5)) `int)))
   1))

(define-dependency-test eigen-tests
  ())

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

   (time (map-tests))
   (time (list-tests))
   (time (dom-tests))
   (time (fd-tests))
   (time (length-tests))
   (time (tree-tests))
   (time (dots-tests))

   (time (stlc-tests))
   (time (eigen-tests))))

(module+ main
  (parameterize ([pretty-print-columns 102])
    (time (void (run-tests builtin-test-suite)))))
