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

(require racket/class racket/list racket/function 
         (except-in racket/match ==))
(require (lib "kraken/src/main.rkt"))
(provide (all-defined-out))

;; =============================================================================
;; dom@

(define dom%
  (class number% 
    (super-new)

    (inherit-field rands)
    (define x (car rands))

    (define/override (get-sexp-rator) 'dom%)

    (define d 
      (cond
       [(not (null? (cdr rands))) (cadr rands)]
       [(value-dom? x) (range-dom x x)]
       [else (range-dom 0 100)]))
    
    (define/public (get-value) d)

    (define/override (update state)
      (let ([x (send state walk x)])
        (cond
         [(null-dom? x) (new fail% [trace this])]
         [(value-dom? x)
          (or (and (memv-dom? x d) succeed)
              (new fail% [trace this]))]
         [(singleton-dom? d)
          (send (== x (singleton-element-dom d)) update state)]
         [else (new dom% [rands (list x d)])])))

    ;; this is the "newer" attr, attr^ was stored before
    (define/augment (merge attr^ state)
      (cond
       [(is-a? attr^ this%)
        (define old-d (send attr^ get-value))
        (define new-d (intersection-dom d old-d))
        (cond
         [(equal? new-d old-d) (send state set-stored attr^)]
         [else
          (define-values (store store^)
            (partition (curryr is-a? +%) (get-field store state)))
          (send (apply conj store)
                run
                (send (new dom% [rands (list x new-d)])
                      run (new state%
                               [subst (get-field subst state)]
                               [store store^])))])]
       [else (send state set-stored this)]))

    (define/override (augment-stream stream)
      (send (apply disj (for/list ([i (dom->list d)]) (≡ x i)))
            augment-stream stream))))

(define (dom@ x d)
  (new dom% [rands (list x d)]))

;; =============================================================================
;; +@

(define (+@ . n*)
  (new +% [rands n*]))

(define +%
  (class* relation% (functionable<%>)
    (super-new)
    (inherit-field [n* rands])

    (define/augment (update state)
      (cond
       [(or (null? n*) (null? (cdr n*))) 
        (new state%)]
       [(null? (cddr n*))
        (== (car n*) (cadr n*))]
       [(null? (cdddr n*))
        (apply update/3 state n*)]
       [else
        (match-define (list n1 n2 rest ...) n*)
        (send
         (exists (n^)
           (conj (+@ n1 n2 n^)
                 (apply +@ (cons n^ rest))))
         update state)]))

    (define (update/3 state u v w)
      (let ([u (send state walk u)]
            [v (send state walk v)]
            [w (send state walk w)])
        (cond
         [(or (var? u) (var? v) (var? w))
          (let ([du (or (send state get-stored dom% u) 
                        (and (value-dom? u) (range-dom u u))
                        (range-dom 0 100))]
                [dv (or (send state get-stored dom% v) 
                        (and (value-dom? v) (range-dom v v))
                        (range-dom 0 100))]
                [dw (or (send state get-stored dom% w) 
                        (and (value-dom? w) (range-dom w w))
                        (range-dom 0 100))])
            (let ([wmin (min-dom dw)] [wmax (max-dom dw)]
                  [umin (min-dom du)] [umax (max-dom du)]
                  [vmin (min-dom dv)] [vmax (max-dom dv)])
              (let ([new-w-dom (range-dom (+ umin vmin) (+ umax vmax))]
                    [new-u-dom (range-dom (- wmin vmax) (- wmax vmin))]
                    [new-v-dom (range-dom (- wmin umax) (- wmax umin))])
                (conj (+@ u v w)
                      (send (conj (dom@ w new-w-dom)
                                  (dom@ v new-v-dom)
                                  (dom@ u new-u-dom))
                            update state)))))]
         [(and (number? u) (number? v) (number? w))
          (or (and (= (+ u v) w) (new state%)) 
              (new fail% [trace this]))]
         [else (new fail% [trace this])])))

    ;; (+@ n*) = out
    (define/public (->out state k)
      (let ([n* (send state walk n*)])
        (cond
         [(andmap number? n*) (apply + n*)]
         [else 
          (define-values (m* x*) (partition number? n*))
          (new this% [rands (cons (apply + m*) x*)])])))

    (define/public (->rel n^ state)
      (let ([n* (send state walk n*)])
        (send (apply +@ (append n* (list n^))) run state)))))

;; =============================================================================
;; dom abstractions

(define (interval? x)
  (pair? x))

(define (interval-union i j)
  (define imin (car i))
  (define imax (cdr i))
  (define jmin (car j))
  (define jmax (cdr j))
  (cond
   [(or (= imax jmin) (= imax (- jmin 1)))
    (range-dom imin jmax)]
   [(or (= jmax imin) (= jmax (- imin 1)))
    (range-dom jmin imax)]
   [(< imax jmin) `(,i ,j)]
   [(< jmax imin) `(,j ,i)]
   [(and (<= imin jmin) (>= imax jmax))
    (range-dom jmin jmax)]
   [(and (<= jmin imin) (>= jmax imax))
    (range-dom jmin jmax)]
   [(and (<= imin jmin) (>= jmax imax))
    (range-dom imin jmax)]
   [(and (<= jmin imin) (>= imax jmax))
    (range-dom jmin imax)]
   [else (error 'interval-union "not defined for ~a ~a" i j)]))

(define (interval-difference i j)
  (define imin (car i))
  (define imax (cdr i))
  (define jmin (car j))
  (define jmax (cdr j))
  (cond
   [(> jmin imax)
    (range-dom imin imax)]
   [(and (<= jmin imin) (>= jmax imax)) 
    `()]
   [(and (< imin jmin) (> imax jmax))
    `((,imin . ,(- jmin 1)) (,(+ jmax 1) . ,imax))]
   [(and (< imin jmin) (<= jmin imax))
    (range-dom imin (sub1 jmin))]
   [(and (> imax jmax) (<= jmin imin))
    (range-dom (add1 jmax) imax)]
   [else (error 'interval-difference "not defined for ~a ~a" i j)]))

(define (interval-intersection i j)
  (define imin (car i))
  (define imax (cdr i))
  (define jmin (car j))
  (define jmax (cdr j))
  (cond
   [(< imax jmin) `()]
   [(< jmax imin) `()]
   [(and (<= imin jmin) (>= imax jmax)) `(,j)]
   [(and (<= jmin imin) (>= jmax imax)) `(,i)]
   [(and (<= imin jmin) (<= imax jmax))
    (range-dom jmin imax)]
   [(and (<= jmin imin) (<= jmax imax))
    (range-dom imin jmax)]
   [else (error 'interval-intersection "not defined for ~a ~a" i j)]))

(define (interval-memq? x intvl)
  (and (>= x (car intvl)) (<= x (cdr intvl))))

(define (interval-combinable? i j)
  (define imin (car i))
  (define imax (cdr i))
  (define jmin (car j))
  (define jmax (cdr j))
  (or (= imax (sub1 jmin))
      (= jmax (sub1 imin))
      (not (or (> jmin imax) (> imin jmax)))))

(define (interval-> i j)
  (> (car i) (cdr j)))

(define (interval-< i j)
  (< (cdr i) (car j)))

(define (singleton-interval? x)
  (= (car x) (cdr x)))

(define (copy-before-interval pred intvl)
  (define min (car intvl))
  (define max (cdr intvl))
  (let loop ([i min])
    (cond
     [(pred i)
      (if (= min i) `() (range-dom min (sub1 i)))]
     [(= i max) `()]
     [else (loop (+ i 1))])))

(define (drop-before-interval pred intvl)
  (define min (car intvl))
  (define max (cdr intvl))
  (let loop ([i min])
    (cond
     [(pred i) (range-dom i max)]
     [(= i max) (list)]
     [else (loop (+ i 1))])))

(define (range-dom lb ub)
  (cond
   [(>= ub 0) `((,(max lb 0) . ,ub))]
   [else `()]))

(define (value-dom? v)
  (and (integer? v) (<= 0 v)))

(define (make-dom n*)
  (let loop ([n* n*])
    (cond
     [(null? n*) (list)]
     [else (cons-dom (car n*) (loop (cdr n*)))])))

(define (car-dom dom)
  (caar dom))

(define (cdr-dom dom)
  (define intvl (car dom))
  (if (singleton-interval? intvl)
      (cdr dom)
      (cons `(,(+ (car intvl) 1) . ,(cdr intvl)) (cdr dom))))

(define (cons-dom x dom)
  (let loop ([x (if (interval? x) x `(,x . ,x))] [dom dom])
    (cond
     [(null-dom? dom) `(,x)]
     [(interval-combinable? x (car dom))
      (append-dom (interval-union x (car dom)) (cdr dom))]
     [(interval-> x (car dom))
      (cons-dom (car dom) (loop x (cdr dom)))]
     [else (cons x dom)])))

(define (append-dom l s)
  (cond
   [(null-dom? l) s]
   [else (cons-dom (car l) (append-dom (cdr l) s))]))

(define (null-dom? x) 
  (null? x))

(define (singleton-dom? dom)
  (and (not (null-dom? dom))
       (null-dom? (cdr dom))
       (singleton-interval? (car dom))))

(define (singleton-element-dom dom)
  (caar dom))

(define (min-dom dom)
  (caar dom))

(define (max-dom dom)
  (cond
   [(null-dom? (cdr dom)) (cdar dom)]
   [else (max-dom (cdr dom))]))

(define (memv-dom? v dom)
  (and (value-dom? v)
       (findf (lambda (d) (interval-memq? v d)) dom)))

(define (intersection-dom dom1 dom2)
  (cond
   [(or (null-dom? dom1) (null-dom? dom2)) '()]
   [(interval-< (car dom1) (car dom2))
    (intersection-dom (cdr dom1) dom2)]
   [(interval-> (car dom1) (car dom2))
    (intersection-dom dom1 (cdr dom2))]
   [else
    (define a1 (interval-difference (car dom1) (car dom2)))
    (define a2 (interval-difference (car dom2) (car dom1)))
    (append-dom
     (interval-intersection (car dom1) (car dom2))
     (intersection-dom
      (append-dom a1 (cdr dom1))
      (append-dom a2 (cdr dom2))))]))

(define (diff-dom dom1 dom2)
  (cond
   [(or (null-dom? dom1) (null-dom? dom2)) dom1]
   [(interval-< (car dom1) (car dom2))
    (cons (car dom1) (diff-dom (cdr dom1) dom2))]
   [(interval-> (car dom1) (car dom2))
    (diff-dom dom1 (cdr dom2))]
   [else
    (define a1 (interval-difference (car dom1) (car dom2)))
    (define a2 (interval-difference (car dom2) (car dom1)))
    (diff-dom
     (append-dom a1 (cdr dom1))
     (append-dom a2 (cdr dom2)))]))

(define (remq-dom x dom)
  (diff-dom dom (make-dom (list x))))

(define (copy-before-dom pred dom)
  (cond
   [(null? dom) '()]
   [(let ((intvl (car dom)))
      (and (pred (cdr intvl)) intvl))
    => (lambda (intvl) (copy-before-interval pred intvl))]
   [else (cons (car dom) (copy-before-dom pred (cdr dom)))]))

(define (drop-before-dom pred dom)
  (cond
   [(null? dom) '()]
   [(let ((intvl (car dom)))
      (and (pred (cdr intvl)) intvl))
    => (lambda (intvl)
         (append (drop-before-interval pred intvl) (cdr dom)))]
   [else (drop-before-dom pred (cdr-dom dom))]))

(define (disjoint-dom? dom1 dom2)
  (cond
   [(or (null? dom1) (null? dom2)) #t]
   [(interval-< (car dom1) (car dom2))
    (disjoint-dom? (cdr dom1) dom2)]
   [(interval-> (car dom1) (car dom2))
    (disjoint-dom? dom1 (cdr dom2))]
   [else #f]))

(define (dom->list d)
  (cond
   [(null-dom? d) '()]
   [else (cons (car-dom d) (dom->list (cdr-dom d)))]))


