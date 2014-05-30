;; Copyright (C) 2013-2014 Claire Alvis
;; Copyright (C) 2011-2013 Daniel P. Friedman, Oleg Kiselyov,
;; Claire E. Alvis, Jeremiah J. Willcock, Kyle M. Carter, William E. Byrd
;;
;; Permission is hereby granted, free of charge, to any person
;; obtaining a copy of this software and associated documentation
;; files (the "Software"), to deal in the Software without
;; restriction, including without limitation the rights to use, copy,
;; modify, merge, publish, distribute, sublicense, and/or sell copies
;; of the Software, and to permit persons to whom the Software is
;; furnished to do so, subject to the following conditions:
;;
;; The above copyright notice and this permission notice shall be
;; included in all copies or substantial portions of the Software.
;;
;; THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
;; EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
;; MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
;; NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
;; BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
;; ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
;; CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
;; SOFTWARE.

#lang racket/base

(require racket/class racket/function)

;; =============================================================================
;; cvars

(provide (struct-out cvar) reify-n)

;; normal miniKanren vars are actually an instance of a more general
;; "constrained var", or cvar for short.
(struct cvar (str x)
        #:transparent
        #:methods gen:custom-write
        [(define (write-proc x port mode)
           (display (format "#~a(~a)" (cvar-str x) (cvar-x x)) port))])

(define (reify-n cvar n)
  (string->symbol (format "~a.~a" (cvar-str cvar) (number->string n))))

;; =============================================================================
;; vars; A LogicVariable (LV) is a (var Symbol)

(provide var var?)

;; defines a normal miniKanren var as a cvar that is printed with "_"
(struct -var cvar (name) #:transparent
        #:methods gen:equal+hash
        [(define (equal-proc x y recur?)
           (and (recur? (-var-name x) (-var-name y))))
         (define (hash-proc x recur)
           (recur (cvar-x x)))
         (define (hash2-proc x recur)
           (recur (cvar-x x)))])
(define (var x) (-var "lv" (gensym x) x))
(define (var? x) (-var? x))

;; =============================================================================
;; placeholders

(provide any any?)

(struct any () #:transparent)

;; =============================================================================
;; eigens

(provide eigen eigen?)

(struct -eigen cvar () #:transparent)
(define (eigen x) (-eigen "e" x))
(define eigen? -eigen?)

;; =============================================================================
;; trees

(provide (struct-out tree))

(struct tree (nodes) #:transparent
        #:methods gen:custom-write
        [(define (write-proc x port mode)
           (display
            (cons 'tree 
                  (for/fold ([nodes '()]) ([node (tree-nodes x)])
                    (cond
                     [(list? node) (append nodes node)]
                     [else (append nodes (list '@ node))])))
            port))])

;; =============================================================================
;; substitution

(provide walk/internal size-s)

(define substitution? list?)

;; the empty association list, abbreviated s
(define empty-s '())
(define empty-s? null?)

(define (ext-s x v s) (cons `(,x . ,v) s))
(define (ext-s* p s) (append p s))

(define (size-s s) (length s))

(define (walk/internal u s)
  (cond
   [(and (cvar? u) (assq u s))
    => (lambda (a) (walk/internal (cdr a) s))]
   [(pair? u)
    (cons (walk/internal (car u) s)
          (walk/internal (cdr u) s))]
   [(tree? u)
    (tree (map (curryr walk/internal s) (tree-nodes u)))]
   [else u]))


;; =============================================================================
;; reification

(provide extend-rs reify-s filter*)

(define (extend-rs v s)
  `((,v . ,(reify-n v (size-s s))) . ,s))

(define (reify-s v^ s)
  (define v (walk/internal v^ s))
  (cond
   [(cvar? v)
    (extend-rs v s)]
   [(pair? v) 
    (reify-s (cdr v) (reify-s (car v) s))]
   [(tree? v)
    (for/fold ([s s]) ([node (tree-nodes v)])
      (reify-s node s))]
   [else s]))

(define (filter* f t)
  (cond
   [(f t) (list t)]
   [(pair? t) (append (filter* f (car t)) (filter* f (cdr t)))]
   [else (list)]))

