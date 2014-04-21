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
   (run succeed)
   (list empty-state)))

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
                          (define/augment (join state)
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
         (associate x (list y))))

  (check-equal?
   (stream-length (send (disj (== x 1) (== x 2))
                        augment-stream (list empty-state)))
   2))

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
   "!= pair-pair different"))

(define-dependency-test operator-tests
  (associate-tests
   conj-tests
   disj-tests
   ;; when-tests
   ))

(define-dependency-test map-tests
  (operator-tests)

  (check-equal? 
   (run (map/o associate (list x) (list y)))
   (run (associate x y))))

(define-dependency-test dom-tests
  (operator-tests)

  (check-equal?
   (run (dom/a x (range-dom 2 2)))
   (run (associate x 2)))

  (check-equal?
   (run (conj (dom/a x (range-dom 1 2)) (dom/a x (range-dom 2 3))))
   (run (dom/a x (range-dom 2 2))))

  (check-equal?
   (length (run (dom/a x (range-dom 4 5))))
   2)

  #;
  (check-equal?
   (run (conj (dom/a x (range-dom 1 10))
              (dom/a x (range-dom 3 7))
              (dom/a x (range-dom 4 5))))
   (run (dom/a x (range-dom 4 5))))

  #;
  (check-equal?
   (run (conj (conj (associate x y)
                    (dom/a z (range-dom 1 2)))
              (conj (associate y z)
                    (dom/a x (range-dom 2 3)))))
   (run (conj (associate x y)
              (associate y z)
              (associate z 2)))))

(define-dependency-test fd-tests
  (operator-tests dom-tests)

  (check-equal?
   (run (+/o x 5 7))
   (run (associate x 2)))

  (check-equal?
   (run (conj (dom/a x (range-dom 1 10))
              (+/o x 5 7)))
   (run (associate x 2)))

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
   (run (list/a (list 1 2 3)))
   (list empty-state))

  (check-equal?
   (run (list/a 4))
   (list)))

(define-dependency-test length-tests
  (operator-tests fd-tests)
  
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
  (let ([state (send (conj (length/a x n1) (length/a y n2) (+/o n1 n2 1))
                     join empty-state)])
    (check-not-false state)

    (let ([answer (send state narrow 3)])
      (check-false (null? answer))
      (check-equal? (length answer) 2 (~a answer)))))

(define-dependency-test tree-tests
  (operator-tests length-tests list-tests)

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

  (let ([answer (run (length/a (tree `(,x)) 2))])
    (check-false (null? answer)))

  (let ([state (send (length/a (tree `(,x ,y)) 2) join empty-state)])
    (check-not-false state)

    (let ([answer (send state narrow 4)])
      (check-false (null? answer))
      (check-true (is-a? (car answer) state%) (~a (car answer)))

      (check-equal?
       (map (lambda (state) (send state reify (list x y))) answer)
       '(((_.0 _.1) ()) ((_.0) (_.1)) (() (_.0 _.1))))))

  (let ([state (send (length/a (tree `(,x (3) ,y)) 3) join empty-state)])
    (check-not-false state)

    (pretty-print state)))

(define builtin-test-suite
  (test-suite 
   "builtin tests"
   
   (time (state-tests))
   (time (associate-tests))
   (time (conj-tests))
   ;; (time (when-tests))
   (time (disj-tests))
   (time (operator-tests))

   (time (map-tests))
   (time (list-tests))
   (time (dom-tests))
   (time (fd-tests))
   (time (length-tests))
   (time (tree-tests))))

(module+ main
  (parameterize ([pretty-print-columns 200])
    (time (void (run-tests builtin-test-suite)))))
