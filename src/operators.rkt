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

(require racket/class racket/function racket/list racket/pretty racket/stream
         (except-in racket/match ==))
(require (for-syntax racket/base syntax/parse racket/syntax))
(require "states.rkt" "data.rkt" "infs.rkt")

(provide (all-defined-out))

;; =============================================================================
;; existentials

(define-syntax-rule (exists (x ...) bodys ... body)
  (let ([x (var 'x)] ...)
    (unless (void? bodys)
      (error 'exists "not void\n expression: ~a" 'bodys))
    ... 
    (send body add-scope (list x ...))))

(define-syntax-rule (fresh (x ...) body ...)
  (exists (x ...) body ...))

;; =============================================================================
;; universals

(define-syntax-rule (forall (x ...) bodys ... body)
  (let ([x (eigen 'x)] ...) 
    (unless (void? bodys)
      (error 'forall "intermediate expression was not void\n ~a" 'bodys))
    ... 
    (send body add-scope (list x ...))))

;; =============================================================================
;; operators

(define operator%
  (class* object% (printable<%>)
    (super-new)

    (define/public (sexp-me) #f)

    (define/public (custom-print p depth)
      (write (sexp-me) p))
    (define/public (custom-write p)
      (write (sexp-me) p))
    (define/public (custom-display p) 
      (write (sexp-me) p))))

;; -----------------------------------------------------------------------------
;; associate

(define (≡ x v) (== x v))

(define (== x v)
  (new ==% [x x] [v v]))

(define ==%
  (class* operator% (equal<%>)
    (init-field x v [scope '()])
    (super-new)

    (define/public (equal-to? obj recur?)
      (or (and (recur? x (get-field x obj))
               (recur? v (get-field v obj)))
          (and (recur? x (get-field v obj))
               (recur? v (get-field x obj)))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code x) (hash-code v)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (+ (* 10 (hash-code x)) (* 100 (hash-code v))))

    (define/override (sexp-me)
      (list (object-name this%) x v))

    (define/public (update state)
      (let ([x (send state walk x)]
            [v (send state walk v)])
        (send (new state%) associate x v scope)))

    (define/public (combine state)
      (send state associate x v scope))

    (define/public (run state)
      (send state associate x v scope))

    (define/public (add-scope ls)
      (new this% [x x] [v v] [scope (cons ls scope)]))

    (define/public (augment state)
      (delay (run state)))))

;; -----------------------------------------------------------------------------

(define lambda%
  (class operator%
    (super-new)
    (init-field sexp init [scope '()])
    (define/override (sexp-me) sexp)
    (define/public (run state)
      (send (send (init) add-scope scope) run state))
    (define/public (update state) 
      (send (send (init) add-scope scope) update state))
    (define/public (add-scope ls)
      (new this% [sexp sexp] [init init] [scope (cons ls scope)]))
    (define/public (combine state)
      (send state set-stored this))
    (define/public (augment state)
      (delay
        (bindm (send (send (init) add-scope scope) run state)
               (lambda (state) (delay (send state augment))))))))

(require (for-syntax racket/pretty))
(define-syntax (lambda@ stx)
  (syntax-parse stx
    [(lambda@
       (~optional (~seq #:name name))
       (args ...) body:expr)
     (define/with-syntax rel-name
       (cond
        [(attribute name) #'(object-name name)]
        [else (pretty-format (car (syntax->list stx)))]))
     (syntax/loc stx
       (lambda (args ...)
         (let ([th (lambda () body)])
           (new lambda% [sexp (list rel-name args ...)] [init th]))))]))

(define conj%
  (class operator%
    (super-new)
    (init-field [clauses '()] [query #f])

    (define/override (sexp-me)
      (cons (object-name this%) clauses))

    (define/public (run state)
      (delay (for/fold ([a-inf state]) ([g clauses])
               (bindm a-inf (lambda (state) (send g run state))))))

    (define/public (all state)
      (delay (bindm (run state) (lambda (state) (send state augment)))))
    
    (define/public (combine state)
      (for/fold ([state state]) ([thing clauses])
        (send thing combine state)))

    (define/public (update state^)
      (send (new state% [store clauses]) update state^))

    (define/public (add-scope ls)
      (define new-clauses
        (map (lambda (thing) (send thing add-scope ls)) clauses))
      (new conj% [clauses new-clauses] [query query]))

    (define/public (add-query t)
      (new this% [clauses clauses] [query t]))

    (define/public (augment state)
      (delay (for/fold ([a-inf state]) ([g clauses])
               (bindm a-inf (lambda (state) (send g augment state))))))))

(define (conj . clauses)
  (new conj% [clauses clauses]))

;; -----------------------------------------------------------------------------
;; disjunction

(define disj%
  (class* operator% (equal<%>)
    (init-field [states '()])
    (super-new)

    (define/override (sexp-me)
      (cons (object-name this%) states))

    (define/public (equal-to? obj recur?)
      (and (= (length states) (length (get-field states obj)))
           (andmap recur? states (get-field states obj))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code states)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (apply + (map (lambda (r i) (* (expt 10 i) (hash-code r)))
                    states (range 0 (length states)))))

    (define/public (update state)
      (define ss (map (lambda (ss) (send ss update state)) states))
      (define result (filter (lambda (state) (not (is-a? state fail%))) ss))
      (cond
       [(null? result) (new fail% [trace `(disj% . ,ss)])]
       [(findf (lambda (ss) (and (is-a? ss state%)
                                 (send ss trivial?)))
               result) 
        succeed]
       [(null? (cdr result)) (car result)]
       [else (new disj% [states result])]))

    (define/public (run state)
      (delay (let loop ([states states])
               (cond
                [(null? (cdr states)) 
                 (send (car states) run state)]
                [else (mplusm (send (car states) run state)
                              (delay (loop (cdr states))))]))))

    (define/public (combine state)
      (cond
       [(send state has-stored this) state]
       [else (send state set-stored this)]))

    (define/public (add-scope ls)
      (new disj% [states (map (lambda (ss) (send ss add-scope ls)) states)]))

    (define/public (augment state)
      (delay (let loop ([states states])
               (cond
                [(null? (cdr states)) 
                 (send (car states) augment state)]
                [else (mplusm (send (car states) augment state)
                              (delay (loop (cdr states))))]))))))

(define (disj . clauses)
  (new disj% [states clauses]))

;; -----------------------------------------------------------------------------
;; implies

(define ==>%
  (class* operator% (equal<%>)
    (super-new)
    (init-field test consequent)

    (define/override (sexp-me)
      (list (object-name this%) test consequent))

    (define/public (equal-to? obj recur?)
      (and (recur? test (get-field test obj))
           (recur? consequent (get-field consequent obj))))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code test) (hash-code consequent)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (+ (hash-code test) (* 10 (hash-code consequent))))

    (define/public (update state)
      (define test^ (send test update state))
      (cond
       [(is-a? test^ state%)
        (cond
         [(send test^ trivial?) 
          (send consequent update state)]
         [(send test^ fail?) test^]
         [else (new ==>% [test test^] [consequent consequent])])]
       [else (new ==>% [test test^] [consequent consequent])]))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (add-scope ls)
      (new this%
           [test (send test add-scope ls)]
           [consequent (send consequent add-scope ls)]))

    (define/public (augment state)
      (delay
        (bindm (send test augment state)
               (lambda (state) (delay (send consequent augment state))))))))

(define (==> t [c succeed]) 
  (new ==>% [test t] [consequent c]))

;; -----------------------------------------------------------------------------
;; not

(define not%
  (class* operator% (equal<%>)
    (super-new)
    (init-field stmt)

    (define/override (sexp-me)
      (list (object-name this%) stmt))

    (define/public (equal-to? obj recur?)
      (recur? stmt (get-field stmt obj)))
    (define/public (equal-hash-code-of hash-code)
      (+ 1 (hash-code stmt)))
    (define/public (equal-secondary-hash-code-of hash-code)
      (hash-code stmt))

    (define/public (update state)
      (define new-stmt (send stmt update state))
      (cond
       [(is-a? new-stmt state%)
        (cond
         [(send new-stmt trivial?)
          (new fail%)]
         [(send new-stmt fail?)
          succeed]
         [else 
          (define newer-stmt
            (append (for/list ([p (get-field subst new-stmt)])
                      (! (new state% [subst `(,p)])))
                    (for/list ([thing (get-field store new-stmt)])
                      (! thing))))
          (if (= (length newer-stmt) 1)
              (new this% [stmt new-stmt])
              (apply disj newer-stmt))])]
       [(is-a? new-stmt disj%)
        (apply disj (map (lambda (state) (new this% [stmt state]))
                         (get-field states new-stmt)))]
       [else (new this% [stmt new-stmt])]))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (add-scope ls)
      (new this% [stmt (send stmt add-scope ls)]))))

(define (! stmt)
  (new not% [stmt (send stmt update (new state%))]))


;; -----------------------------------------------------------------------------

(define project%
  (class operator%
    (super-new)
    (init-field term pattern phase1 phase2)

    (define/override (sexp-me)
      (list (object-name this%) term pattern))

    (define/public (update state)
      (let ([t (send state walk term)])
        (cond
         [(var? t) this]
         [(phase1 t)
          => (lambda (this^)
               (cond
                [(boolean? this^) this]
                [else (send this^ update state)]))]
         [else (new fail% [trace this])])))

    (define/public (augment state)
      (let ([t (send state walk term)])
        (send (phase2 t) augment state)))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (add-scope ls) this)))

(require (for-syntax racket/function))

(define-for-syntax (walk-pattern stx quoted?)
  (syntax-parse stx
    [((~literal unquote) x:id)
     #:fail-unless quoted? "unquote not inside quasiquote"
     (list #'x)]
    [((~literal quasiquote) expr)
     (walk-pattern #'expr #t)]
    [((~literal cons) a d)
     (append (walk-pattern #'a quoted?)
             (walk-pattern #'d quoted?))]
    [((~literal list) . d)
     (apply append (map (curryr walk-pattern quoted?)
                        (syntax->list #'d)))]
    [(a . d)
     (append (walk-pattern #'a quoted?)
             (walk-pattern #'d quoted?))]
    [x (if quoted? (list) (list #'x))]))

(require (for-syntax racket/pretty))

(define-for-syntax (commit-pattern stx thing quoted?)
  (syntax-parse stx
    [((~literal unquote) x:id)
     #:fail-unless quoted? "unquote not inside quasiquote"
     #'#t]
    [((~literal quasiquote) expr)
     #:when (not quoted?)
     (commit-pattern #'expr thing #t)]
    [((~literal cons) a d)
     #:when (not quoted?)
     #`(or (var? #,thing)
           (and (pair? #,thing) 
                #,(commit-pattern #'a #`(car #,thing) quoted?)
                #,(commit-pattern #'d #`(cdr #,thing) quoted?)))]
    [((~literal list))
     #`(null? #,thing)]
    [(a . d)
     #:fail-unless quoted? "expected constructor"
     #`(or (var? #,thing)
           (and (pair? #,thing) 
                #,(commit-pattern #'a #`(car #,thing) quoted?)
                #,(commit-pattern #'d #`(cdr #,thing) quoted?)))]
    [x:id
     (cond
      [quoted? #`(or (var? #,thing) (eq? #,thing 'x))]
      [else #`t])]
    [() 
     #:fail-unless quoted? "app"
     #`(or (var? #,thing) (null? #,thing))]))

(define-syntax (project stx)
  (syntax-parse stx
    [(project project-term:id
       [pat (~optional body #:defaults ([body #'succeed]))]
       ...)
     (define/with-syntax ((vars ...) ...)
       (map (curryr walk-pattern #f)
            (syntax->list #'(pat ...))))
     (define/with-syntax (hope? ...)
       (map (curryr commit-pattern #'t #f)
            (syntax->list #'(pat ...))))
     (define/with-syntax (phase1-body ...)
       #'((lambda (t) (match t [pat body] [_ hope?]))
          ...))
     (define/with-syntax (phase2-body ...)
       #'((lambda (t)
            (exists (vars ...) 
              (conj (== t pat) 
                    (let ([project-term pat]) body))))
          ...))
     #'(disj
        (new project%
             [term project-term] 
             [pattern 'pat]
             [phase1 phase1-body]
             [phase2 phase2-body])
        ...)]))

