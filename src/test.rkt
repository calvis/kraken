#lang racket

(require (except-in rackunit fail) rackunit/text-ui) 
(require "main.rkt")

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

(define x (var 'x))
(define y (var 'y))
(define z (var 'z))

(define-dependency-test state-tests
  ()

  (check-equal?
   (new state% [s `((,x . 5))])
   (new state% [s `((,x . 5))]))

  (check-equal?
   (take (send succeed join empty-state))
   (list empty-state))

  (check-equal?
   (run succeed)
   (take (send succeed join empty-state))))

(define-dependency-test associate-tests
  (state-tests)

  (check-equal?
   (run (associate x 5))
   (list (new state% [s `((,x . 5))]))
   "associate var-int")
  
  (check-equal?
   (run (associate 5 x))
   (run (associate x 5))
   "associate int-var")
  
  (check-equal?
   (run (associate 5 (cons 1 2)))
   (run fail)
   "associate int-list")

  (check-equal?
   (run (associate (cons 1 2) 5))
   (run fail)
   "associate list-int")

  (check-equal?
   (run (associate x (cons 1 2)))
   (list (new state% [s `((,x . ,(cons 1 2)))]))
   "associate var-list")

  (check-equal?
   (run (associate (cons 1 2) x))
   (run (associate x (cons 1 2)))
   "associate list-var")

  (check-equal?
   (run (associate '() '()))
   (list empty-state))

  (check-equal? 
   (run (associate x '()))
   (list (new state% [s `((,x . ()))]))))

(define-dependency-test conj-tests 
  (associate-tests)

  (check-equal?
   (run (conj (associate x 5)))
   (run (associate x 5))
   "conj one clause")
  
  (check-equal?
   (run (conj (conj (conj (conj (conj (associate x 5)))))))
   (run (associate x 5))
   "conj silly nesting")
  
  (check-equal?
   (run (conj (associate x 5)
              (associate x 5)))
   (run (conj (associate x 5)))
   "conj identical clauses")
  
  (check-equal?
   (run (associate (cons 1 2) (cons 3 4)))
   (run fail)
   "associate different list-list")

  (check-equal?
   (run (associate (list 1 2) (list 1 2)))
   (run (conj (associate 1 1) (associate 2 2)))
   "associate lists as conj associates")

  (check-equal? (run (conj fail)) (run fail))

  (let ([state (run (conj (associate (cons (var 'a) (var 'd)) x)
                          (associate x (list 1 2 3))))])
    (check-not-false state)))

(define-dependency-test when-tests
  (associate-tests conj-tests)

  (check-equal? 
   (run (when succeed (associate x 5)))
   (run (associate x 5))
   "when succeed")

  (check-equal?
   (run (when fail (associate x 5)))
   (run succeed)
   "when fail")

  (define z (var 'z))
  (check-equal?
   (run (conj (when (conj (associate x 5)
                          (associate y 6))
                (associate z 4))
              (associate x 5)
              (associate y 6)))
   (run (conj (associate x 5)
              (associate y 6)
              (associate z 4))))

  (check-equal?
   (run (conj (when (associate x 5)
                (associate z 4))
              (associate x y)
              (associate y 5)))
   (run (conj (associate x y)
              (associate y 5)
              (associate z 4))))

  (check-equal?
   (run (conj (associate x y)
              (when (associate x 5)
                (associate z 4))
              (when (associate z 4)
                succeed)))
   (run (conj (associate x y)
              (when (associate y 5)
                (associate z 4))
              (when (associate z 4)
                succeed))))

  (check-equal?
   (run (when fail (new (class constraint%
                          (super-new)
                          (define/public (join state)
                            (join state))))))
   (run succeed)
   "termination check"))

(define-dependency-test disj-tests
  (associate-tests)

  (check-equal?
   (disj (associate x 5))
   (associate x 5)
   "disj one clause")

  (check-equal? 
   (conj (disj (associate x 5))
         (associate x 5))
   (associate x 5)
   "conj disj associate nesting")
  
  (check-equal? 
   (conj (disj (associate x 5)
               (associate x 6))
         (associate x 5))
   (associate x 5)
   "disj impossible clause")

  (define n (var 'n))

  (check-equal?
   (conj (disj (conj (associate n 0)
                     (associate x '()))
               (conj (associate n 1)
                     (associate x (list y))))
         (associate n 1))
   (conj (associate n 1)
         (associate x (list y)))))

(define-dependency-test atomic-tests
  (conj-tests when-tests associate-tests)

  (check-equal? 
   (conj (atomic x) (associate x 5))
   (associate x 5)
   "atomic associate")
  
  (check-equal? 
   (conj (atomic x) (when (atomic x) (associate x 5)))
   (conj (atomic x) (associate x 5))
   "atomic associate when")
  
  (check-equal? 
   (conj (when (atomic x) (associate x 5)) (atomic x))
   (conj (associate x 5) (atomic x))
   "when atomic associate")
  
  (check-equal? 
   (conj (when (atomic x)
           (associate x 5))
         (atomic y)
         (associate y x))
   (conj (associate x 5) (associate y x))
   "atomic associate chaining"))

(define-dependency-test !=-tests
  (associate-tests conj-tests disj-tests)

  (check-equal?
   (!= 5 6)
   succeed
   "!= int-int different")

  (check-equal?
   (!= 5 5)
   fail
   "!= int-int same")

  (check-equal?
   (!= x x)
   fail
   "!= var-var same")

  (check-equal?
   (!= (cons 1 2) (cons 1 2))
   fail
   "!= pair-pair same")

  (check-equal?
   (!= 5 (cons 1 2))
   succeed
   "!= int-pair")

  (check-equal?
   (!= (cons 1 2) 5)
   succeed
   "!= pair-int")

  (check-equal?
   (car (!= (cons 1 2) (cons 3 4)))
   (car succeed)
   "!= pair-pair different")

  (check-equal?
   (reify (!= (cons x 1) (cons y 1)))
   (reify (!= x y))
   "!= simplify same conclusions")

  (check-equal?
   (reify (!= (cons x 1) (cons y 2)))
   (reify succeed)
   "!= pair-pair var trivial"))

(define-dependency-test dom-tests
  (state-tests associate-tests conj-tests)

  (check-equal?
   (dom x (range 2 2))
   (associate x 2))

  (check-equal?
   (conj (dom x (range 1 2)) (dom x (range 2 3)))
   (dom x (range 2 2)))

  (check-equal?
   (conj (dom x (range 1 10))
         (dom x (range 3 7))
         (dom x (range 4 5)))
   (dom x (range 4 5)))

  (check-equal?
   (conj (conj (associate x y)
               (dom z (range 1 2)))
         (conj (associate y z)
               (dom x (range 2 3))))
   (conj (associate x y)
         (associate y z)
         (associate z 2))))

(define-dependency-test operator-tests
  (associate-tests
   conj-tests
   disj-tests
   when-tests))

(define-dependency-test fd-tests
  (operator-tests)

  (check-equal?
   (+fd x 5 7)
   (associate x 2))

  (check-equal?
   (conj (dom x (range 1 10))
         (+fd x 5 7))
   (associate x 2))

  (check-equal?
   (conj (+fd x 5 7)
         (dom x (range 1 10)))
   (conj (dom x (range 1 10))
         (+fd x 5 7))))

(define-dependency-test length-tests
  (operator-tests fd-tests)
  
  (check-not-false
   (length/a (list 1 2 3) 3))

  (let ([state (length/a (list 1 2 3) x)])
    (check-not-false state)
    (check-equal? (send state walk x) 3
                  (~a state)))

  (check-equal?
   (length (send (length/a x 3) walk x))
   3))

(define-dependency-test list-tests
  (operator-tests))

(define-dependency-test tree-tests
  (operator-tests length-tests list-tests)

  (let ([state (length/a (tree `()) 0)])
    (check-not-false state))

  (let ([state (length/a (tree `(,x)) 2)])
    (check-not-false state)
  
    (check-not-false (list? (send state walk x)))
  
    (check-equal? (length (send state walk x)) 2))
  
  (let ([state (length/a (tree `(,x ,y)) 2)])
    (check-not-false state))

  (check-not-false
   (tree-unify (tree '()) '()))

  (check-not-false
   (tree-unify (tree '()) x))

  (check-equal?
   (send (tree-unify (tree '()) x) walk x)
   (send (associate x '()) walk x))

  (define z (var 'z))
  (check-equal?
   (tree-unify (tree `(,x (3) ,y)) z)
   '?
   ))

(define builtin-test-suite
  (test-suite 
   "builtin tests"
   
   (state-tests)
   (associate-tests)
   (conj-tests)
   (when-tests)
   ;; (dom-tests)
   ;; (disj-tests)
   ;; (operator-tests)
   ;; (fd-tests)
   ;; (length-tests)
   ;; (list-tests)
   ;; (tree-tests)
   ))

(module+ main
  (parameterize ([pretty-print-columns 200])
    (time (void (run-tests builtin-test-suite)))))
