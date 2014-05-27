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

(require racket/class racket/function racket/list racket/pretty
         racket/stream racket/promise)
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

    (define/public (augment result)
      (map-result (lambda (state) (send state associate x v scope)) result))))

;; -----------------------------------------------------------------------------
;; conjunction

(define conj%
  (class operator%
    (super-new)
    (init-field [clauses '()] [query #f])
    
    (define/override (sexp-me)
      (cons (object-name this%) clauses))

    (define/public (run state)
      (define result
        (for/fold ([state state]) ([thing clauses])
          (send thing run state)))
      (if query (send result add-query query) result))
    
    (define/public (combine state)
      (for/fold ([state state]) ([thing clauses])
        (send thing combine state)))

    (define/public (update state^)
      (send (run (new state%)) update state^))

    (define/public (add-scope ls)
      (define new-clauses 
        (map (lambda (thing) (send thing add-scope ls)) clauses))
      (new conj% [clauses new-clauses] [query query]))
    
    (define/public (add-query t)
      (new this% [clauses clauses] [query t]))

    (define/public (augment result)
      (let loop ([clauses clauses] [result result])
        (cond
         [(null? clauses) result]
         [(fail-result? result) fail-result]
         [else (delay (loop (cdr clauses) (send (car clauses) augment result)))])))))

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
      (send (update state) combine state))
    (define/public (combine state)
      (cond
       [(send state has-stored this) state]
       [else (send state set-stored this)]))

    (define/public (augment result)
      (result-interleave
       (map (lambda (state) (send state augment result)) states)))

    (define/public (add-scope ls)
      (new disj% [states (map (lambda (ss) (send ss add-scope ls)) states)]))))

;; [List-of Result] -> Result
(define (result-interleave result*)
  (printf "result-interleave:\n")
  (printf " result*: ~a\n" result*)
  (cond
   [(null? result*) fail-result]
   [else (let loop ([r* result*] [r*^ '()])
           (printf " r*: ~a\n" r*)
           (printf " r*^: ~a\n" r*^)
           (cond
            [(null? r*) (result-interleave (reverse r*^))]
            [else (let ([p (force (car r*))])
                    (printf " p: ~a\n" p)
                    (cond
                     [(not p) (loop (cdr r*) r*^)]
                     [else 
                      (let ([ans (delay (cons (car p) 
                                              (loop (cdr r*) (cons (cdr p) r*^))))])
                        (printf " ans: ~a\n" ans) ans)]))]))]))

(define (disj . clauses)
  (new disj% [states clauses]))

(define (stream-interleave ls)
  (let ([ls (filter (compose not stream-empty?) ls)])
    (cond
     [(null? ls) empty-stream]
     [else
      (let loop ([ls^ ls])
        (cond
         [(null? ls^) (stream-interleave (map stream-rest ls))]
         [else (stream-cons (stream-first (car ls^))
                            (loop (cdr ls^)))]))])))

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
       [(send test^ trivial?) 
        (send consequent update state)]
       [(send test^ fail?) test^]
       [else (new ==>% [test test^] [consequent consequent])]))

    (define/public (run state)
      (send (update state) combine state))
    (define/public (combine state)
      (send state set-stored this))

    (define/public (add-scope ls)
      (new this%
           [test (send test add-scope ls)]
           [consequent (send consequent add-scope ls)]))

    (define/public (augment result)
      (let ([result (filter-result (send test augment result))])
        (if (fail-result? result) 
            result 
            (send consequent augment result))))))

(define (==> t [c succeed]) 
  (new ==>% 
       [test (send t run (new state%))]
       [consequent c]))

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
