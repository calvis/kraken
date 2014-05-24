#lang racket/base

(require (for-syntax racket/base syntax/parse))
(require racket/class 
         (except-in racket/match ==)
         racket/list
         racket/function
         racket/pretty
         racket/stream)

(require "data.rkt"
         "states.rkt"
         "interfaces.rkt"
         "operators.rkt")

(provide (all-from-out "data.rkt")
         (all-from-out "states.rkt")
         (all-from-out "operators.rkt")
         (all-from-out "interfaces.rkt")
         (all-defined-out))

;; =============================================================================
;; constraints and attributes

(define base%
  (class* object% (printable<%> 
                   streamable<%>
                   runnable<%>
                   updateable<%>
                   combineable<%>)
    (super-new)

    (init-field [rator this%] [rands '()] [scope '()])

    (define/public (get-rator) this%)
    (define/public (get-rands) rands)

    (define/public (custom-print p depth)
      (display (cons (object-name this%) rands) p))
    (define/public (custom-write p)
      (write   (cons (object-name this%) rands) p))
    (define/public (custom-display p) 
      (display (cons (object-name this%) rands) p))

    (define/public (update-rands rands)
      (new this% [rands rands] [scope scope]))

    (define/public (run state)
      (send (send this update state) combine state))

    (define/pubment (update state)
      (call/cc
       (lambda (k)
         (let ([rands^ (map (update-functionable state k) rands)])
           (cond
            [(findf (curryr is-a? functionable<%>) rands^)
             (update-rands rands^)]
            [(andmap eq? rands rands^)
             (inner this update state)]
            [else (send (update-rands rands^) update state)])))))

    (define/public (add-scope ls)
      (new this% [rands rands] [scope (cons ls scope)]))

    ;; State Stream -> Stream
    (define/public (augment-stream stream)
      (stream-filter
       (compose not (curryr is-a? fail%))
       (stream-map 
        (lambda (state)
          (call/cc 
           (lambda (k)
             (let ([rands (map (update-functionable state k) rands)])
               (cond
                [(findf (curryr is-a? functionable<%>) rands)
                 (define-values (new-state new-rands)
                   (for/fold ([state state] [rands '()]) ([r rands])
                     (cond
                      [(is-a? r functionable<%>)
                       (let ([out (var 'out)])
                         (values (send r ->rel out state)
                                 (cons out rands)))]
                      [else (values state (cons r rands))])))
                 (send (send this update-rands (reverse new-rands))
                       run new-state)]
                [else (send this run state)])))))
        stream)))

    (define/public (combine state)
      (send state set-stored this))))

(define ((update-functionable state k) r)
  (if (is-a? r functionable<%>) (send r ->out state k) r))

(define relation% 
  (class* base% (equal<%>)
    (super-new)
    (inherit-field rands)

    (define/public (equal-to? obj recur?)
      (and (= (length rands) (length (get-field rands obj)))
           (andmap recur? rands (get-field rands obj))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code rands)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    rands (range 0 (length rands)))))))

(define empty-state (new state%))

;; =============================================================================
;; examples

(define shape%
  (class relation%
    (super-new)
    (inherit-field rands)
    (match-define (list x t) rands)

    (define/augment (update state)
      (let ([x (send state walk x)]
            [t (send state walk t)])
        (cond
         [(any? t) state]
         [(and (pair? x) (pair? t))
          (send (conj (shape (car x) (car t))
                      (shape (cdr x) (cdr t)))
                update state)]
         [(symbol? t) (== x t)]
         [(null? t) (== x `())]
         [(and (not (var? x)) (pair? t)) 
          (new fail% [trace this])]
         [else (shape x t)])))))

(define (shape x t) (new shape% [rands (list x t)]))

(define-syntax-rule (case-shape x [t clause] ...)
  (disj (==> (shape x `t) clause) ...))

(define (run obj [n #f])
  (cond
   [(send (conj obj) run (new state%))
    => (lambda (state) (send state narrow n))]
   [else '()]))

(define cdr%
  (class* relation% (functionable<%>)
    (super-new)
    (inherit-field rands)

    (define ls (car rands))

    (define/public (->out state k)
      (let ([ls (send state walk
                      ((update-functionable state k) ls))])
        (cond
         [(pair? ls) (cdr ls)]
         [(not (or (object? ls) (var? ls))) 
          (k (new fail% [trace this]))]
         [else (cdr@ ls)])))

    (define/public (->rel v state)
      (send (cdr@ ls v) update state))

    (define/augment (update state)
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) (== (cdr ls) out)]
         [else (cdr@ ls out)])))))

(define (cdr@ . rands)
  (new cdr% [rands rands]))

(define car%
  (class* relation% (functionable<%>)
    (super-new)
    (inherit-field rands)

    (define ls (car rands))

    (define/public (->out state k)
      (let ([ls (send state walk ((update-functionable state k) ls))])
        (cond
         [(pair? ls) (car ls)]
         [(not (or (var? ls) (object? ls))) 
          (k (new fail% [trace this]))]
         [else (car@ ls)])))

    (define/public (->rel v state)
      (let ([ls (send state walk ls)])
        (send (car@ ls v) run state)))

    (define/augment (update state)
      (let ([ls (send state walk ls)]
            [out (send state walk (cadr rands))])
        (cond
         [(pair? ls) (== (car ls) out)]
         [else (car@ ls out)])))))

(define (car@ . rands)
  (new car% [rands rands]))

(define (partial-mixin %)
  (class* % (printable<%>)
    (super-new)
    (inherit-field rands)
    (init-field [partial #f])

    (define/override (custom-print p depth)
      (display (list (object-name this%) rands partial) p))
    (define/override (custom-write p)
      (write   (list (object-name this%) rands partial) p))
    (define/override (custom-display p) 
      (display (list (object-name this%) rands partial) p))

    (define/public (update-partial partial)
      (new this% [rands rands] [partial partial]))

    (define/augride (update state)
      (define new-partial
        (or partial (send this body . rands)))
      (define result (send new-partial update state))
      (cond
       [(is-a? result disj%)
        (send this update-partial result)]
       [else result]))))

(define-syntax (define@ stx)
  (syntax-parse stx
    [(define@ (name@ args ...) interp)
     (define name%
       (quasisyntax/loc #'name
         (partial-mixin
          (class relation%
            (super-new)
            (define/public (body args ...) interp)))))
     #`(define (name@ args ...)
         (new #,name% [rands (list args ...)]))]))

#;
(define-syntax (query stx)
  (syntax-parse stx
    [(query (x) body)
     #'(run (exists (x) (send body term-query x)))]
    [(query (x ...) body)
     #'(run (exists (x ...) (send body term-query (list x ...))))]))

(define attribute%
  (class* base% (equal<%>)
    (super-new)
    (inherit-field rands)

    (define/public (equal-to? obj recur?)
      (and (or (implementation? 
                (send obj get-rator)
                (class->interface this%))
               (implementation? 
                this%
                (class->interface (send obj get-rator))))
           (eq? (car rands) (car (get-field rands obj)))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code rands)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    rands (range 0 (length rands)))))

    (define/override (combine state)
      (cond
       [(send state has-stored this)
        => (lambda (this^)
             ;; we have two identical attributes on the same variable,
             ;; see if they need to merge and take appropriate actions
             (send this merge this^ (send state remove-stored this^)))]
       [else (send state set-stored this)]))))

(define unary-attribute%
  (class attribute% 
    (super-new)

    (define/public (merge a state)
      (cond
       [(implementation? (send a get-rator) (class->interface this%))
        (send state set-stored a)]
       [else (send state set-stored this)]))))

(define binary-attribute%
  (class attribute% 
    (super-new)))

