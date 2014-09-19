#lang scribble/manual

@(require (for-label racket/base racket/class (lib "kraken/main.rkt")))

@(require kraken scribble/eval)

@title{Functional-Logical Programming in Kraken}
@author[@author+email["Claire Alvis" "calvis@ccs.neu.edu"]]

@defmodule[kraken #:lang]

Kraken is a functional-logic programming language.  It is an attempt
to integrate ideas from
@hyperlink["http://miniKanren.org"]{miniKanren} and
@hyperlink["http://racket-lang.org"]{Racket} in the smoothest way
possible.  Although it is a spiritual successor to cKanren and
miniKanren, Kraken does not make any attempt to be backwards
compatible.

@(define kr-eval (make-base-eval))
@(interaction-eval #:eval kr-eval (require kraken))

@section{States}

@defclass[state% object% ()]{ 

Encapsulates information about logical statements.  Each
@racket[state%] contains a substitution that maps variables to values
they have been unified with, and a @racket[store] that contains
statements that are currently in play.}

@section[#:tag "vars"]{Variables}

@defform[(exists (x ...) side-effect-expr ... stmt)
         #:contracts ([side-effect-expr void?]
                      [stmt statement?])]{

Introduces each @racket[x] as a new lexically-scoped (existential)
logic variable, evaluates each @racket[side-effect-expr] and discards
their result.  Then, it adds each @racket[x] to the scope of
@racket[stmt] and returns it.}

@defform[(forall (e ...) side-effect-expr ... stmt)
         #:contracts ([side-effect-expr void?]
                      [stmt statement?])]{

Identical to @racket[exists] except it introduces each @racket[e] as a
new lexically-scoped universal quantification (skolemization)
variable.}

@section[#:tag "eval"]{Evaluation}

@defproc[(run [stmt statement?] [num number? #f]) (list-of state?)]{

Evaluates the logical meaning of @racket[stmt], and returns the first
@racket[num] different possible satisfying @racket[state%]s (or all
of them if no number is given).}

@defform[(query maybe-num (x ...) stmt)
         #:contracts ([stmt statement?])]{

Combines @racket[exists] and @racket[run] to automatically reify each
@racket[x] in the @racket[state%]s resulting from running
@racket[stmt].  If it is supplied, @racket[maybe-num] is passed as the
second argument to @racket[run]. }

@section{Operators} 

Operators are the basic units that combine values, relations, and
other operators into complex logical statements.  Each operator
returns a @racket[statement?] that can be used as an argument to other
operators, or @racket[run] to evaluate its logical meaning in the form
of a @racket[state%]. 

@deftogether[(@defthing[succeed statement?]
              @defthing[fail statement?])]{

The simplest succeding and failing statements are logically equivalent
to true and false.  

@examples[
#:eval kr-eval
(run succeed)
(run fail)
]
}

@deftogether[(@defproc[(≡ [x value?] [v value?]) statement?]
              @defproc[(== [x value?] [v value?]) statement?])]{

Unifies @racket[x] with @racket[v].  

@examples[
#:eval kr-eval
(query (x) (≡ x "(╯°□°）╯︵ ┻━┻"))
]}

@defproc[(conj [clause statement?] ...) statement?]{

Performs logical conjunction over @racket[clause]s.

@examples[
#:eval kr-eval
(query (x y) (conj (≡ x y) (≡ y 5)))
]}

@defproc[(disj [clause statement?] ...) statement?]{

Performs logical disjunction over @racket[clause]s.

@examples[
#:eval kr-eval
(query (x y) (disj (≡ x y) (≡ y 5)))
]}

@defform[(project lv [pattern maybe-body] ...)
         #:grammar ([maybe-body (code:line) body]
                    [pattern (quasiquote quasi-pattern)
                             (cons pattern pattern)
                             (tree (list pattern ...))
                             (list pattern ...)
                             identifier
                             literal]
                    [quasi-pattern (quasi-pattern ...)
                                   (unquote pattern)
                                   symbol])
         #:contracts ([body statement?]
                      [literal value?])]{

A @racket[statement?] that lexically binds @racket[lv] to the value it
has been unified with and then runs @racket[body].  If @racket[lv] is
never unified, it is disjunctively force-unified with each
@racket[pattern].  Each @racket[identifier] in the pattern is also
lexically bound within the @racket[body].

@examples[
#:eval kr-eval
(query (x y) 
  (conj (project x [(list) (≡ y 5)]) 
        (≡ x (list))))
(query (x y) 
  (conj (project x [(list) (≡ y 5)])
        (≡ x 5)))
(query (x y) 
  (project x [(cons a d) (≡ y 5)]))
(query (x)
  (project x 
    [(cons a d) (conj (≡ a 5) (== (cdr x) 6))] 
    [(list x y z) (≡ y 7)]))
]

If a @racket[body] is not provided, @racket[succeed] is simply
substituted in its place.

@examples[
#:eval kr-eval
(query (x) 
  (project x [(tree (list a b))]))
]}

@section{Relations}

@defform[(lambda@ (args ...) body)
         #:contracts ([body statement?])]{

Returns a relation that parameterizes @racket[body] over the
@racket[args].  

@examples[
#:eval kr-eval
(define smile
  (lambda@ (x)
    (disj (≡ x ":)")
          (≡ x ":-)"))))
(exists (x) (smile x))
(query (x) (smile x))
]}

@defform[(define@ (name args ...) body)
         #:contracts ([body statement?])]{

Defines a relation called @racket[name] where @racket[name] is used
for error reporting and printing.

@examples[
#:eval kr-eval
(define@ (lookup@ gamma x t)
  (project gamma
    [(cons a d)
     (disj (≡ a `(,x . ,t))
           (exists (y s)
             (conj (≡ a `(,y . ,s))
                   (lookup@ d x t))))]))
(exists (x) (lookup@ `((y . int)) x `bool))
(query (x) (lookup@ `((y . int)) x `int))
(query (x y) (lookup@ `((,x . bool)) y `bool))
]}

