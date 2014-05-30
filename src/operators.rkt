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
(require "states.rkt" "data.rkt")

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
      (display (sexp-me) p))
    (define/public (custom-write p)
      (write   (sexp-me) p))
    (define/public (custom-display p) 
      (display (sexp-me) p))))

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

(define-syntax (lambda@ stx)
  (syntax-parse stx
    [(lambda@ (args ...) body:expr)
     #'(lambda (args ...)
         (let ([init (lambda () body)])
           (new (class operator%
                  (super-new)
                  (init-field [scope '()])
                  (define/override (sexp-me)
                    init)
                  (define/public (run state)
                    (send (send (init) add-scope scope) run state))
                  (define/public (update state) 
                    (send (send (init) add-scope scope) update state))
                  (define/public (add-scope ls)
                    (new this% [scope (cons ls scope)]))
                  (define/public (combine state)
                    (send state set-stored this))
                  (define/public (augment state)
                    (delay
                      (bindm (send (send (init) add-scope scope) run state)
                             (lambda (state) (delay (send state augment))))))))))]))

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
    (init-field t)

    (define/public (update state)
      (let ([t (send state walk t)])
        (cond
         [(var? t) this]
         [(send this phase1 t)
          => (lambda (this^)
               (send this^ update state))]
         [else (send fail update state)])))

    (define/public (augment state)
      (let ([t (send state walk t)])
        (cond
         [(var? t) 
          (send (send this phase2 t) augment state)]
         [(send this phase1 t)
          => (lambda (this^)
               (send this^ augment state))]
         [else (send fail augment state)])))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (add-scope ls) this)))

(define-for-syntax (walk-pattern stx)
  (syntax-parse stx
    [((~literal unquote) x:id)
     (list #'x)]
    [(a . d)
     (append (walk-pattern #'a)
             (walk-pattern #'d))]
    [x (list)]))

(require (for-syntax racket/pretty))
(define-syntax (project stx)
  (syntax-parse stx
    [(project term:id [pat body] ...)
     (define/with-syntax ((vars ...) ...)
       (map walk-pattern (syntax->list #'(pat ...))))
     #'(new (class project%
              (super-new)
              (define/public (phase1 t)
                (match t [pat body] ... [_ #f]))
              (define/public (phase2 t)
                (disj 
                 (exists (vars ...) 
                   (conj (== t pat) 
                         (let ([term pat]) body)))
                 ...)))
            [t term])]))

