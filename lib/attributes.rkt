#lang racket/base

(require racket/class
         (except-in racket/match ==))
(require "../src/main.rkt"
         "../lib/fd.rkt")
(provide (all-defined-out))

;; =============================================================================
;; partial-attribute-mixin

(define (partial-attribute-mixin %)
  (class* % (printable<%>)
    (super-new)
    (inherit-field rands)
    (init-field [partial #f])

    (define sexp-me 
      (cons (object-name this%) 
            (append rands (if partial (list partial) (list)))))
    (define/override (custom-print p depth)
      (display sexp-me p))
    (define/override (custom-write p)
      (write   sexp-me p))
    (define/override (custom-display p) 
      (display sexp-me p))

    (define/override (update-rands rands)
      (new this% [rands rands] [partial partial]))

    (define/public (update-partial partial)
      (new this% [rands rands] [partial partial]))

    (define/override (update state)
      (define new-partial
        (or partial (send this body . rands)))
      (define result (send new-partial update state))
      (cond
       [(is-a? result disj%)
        (send this update-partial result)]
       [else result]))))

;; =============================================================================
;; tree@

(define tree%
  (class unary-attribute%
    (super-new)

    (inherit-field rands)

    (define/augride (update state)
      (let* ([t (send state walk (car rands))])
        (cond
         [(list? t) 
          (send (new list% [rands (list t)]) update state)]
         [(send state has-stored (list@ t)) succeed]
         [(tree? t)
          (match-define (tree nodes) t)
          (send
           (apply conj (for/list ([node nodes]) (tree/a node)))
           update state)]
         [(var? t) this]
         [else fail])))))

(define (tree/a t)
  (new tree% [rands (list t)]))

;; =============================================================================
;; list@

(define list%
  (partial-attribute-mixin
   (class tree%
     (super-new)
     (define/public (body ls)
       (disj (==> (shape ls (list)))
             (==> (shape ls (cons (any) (any)))
                  (list@ (cdr@ ls))))))))

(define (list@ ls)
  (new list% [rands (list ls)]))

;; =============================================================================
;; dots@

(define dots%
  (class list%
    (super-new)
    (define/override (body ls fn)
      (disj (==> (shape ls (list)))
            (==> (shape ls (cons (any) (any)))
                 (conj (fn (car@ ls)) (dots@ fn (cdr@ ls))))))))

(define (dots@ fn ls)
  (new dots% [rands (list ls fn)]))

;; =============================================================================
;; length@

(define length%
  (class binary-attribute%
    (super-new)
    (inherit-field rands)
    (define x (car rands))

    (define/augment (update state)
      (cond
       [(send state get-stored this% x)
        => (lambda (n) (== (cadr rands) n))]
       [else
        (let ([x (send state walk x)]
              [n (send state walk (cadr rands))])
          (cond
           [(and (list? x) (number? n))
            (or (and (= (length x) n) succeed) fail)]
           [(list? x)
            (== (length x) n)]
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
            (== (for/list ([i n]) (var (gensym 'i))) x)]
           [else (conj (tree/a x) (new this% [rands (list x n)]))]))]))
    
    (define/public (get-value)
      (cond
       [(null? (cdr rands))
        (if (list? x) (length x) (range-dom 0 100))]
       [else (cadr rands)]))))

(define (length@ ls n) 
  (new length% [rands (list ls n)]))

