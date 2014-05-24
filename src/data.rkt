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
(struct -var cvar () #:transparent)
(define (var x) (-var "_" x))
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

