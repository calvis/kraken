#lang scribble/manual

@(require (for-label racket/base racket/class (lib "kraken/main.rkt")))

@(require kraken scribble/eval)

@title{Functional-Logical Programming in Kraken}

@defmodule[kraken #:lang]

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

@defform[(query maybe-num (x ...) side-effect-expr ... stmt)
         #:contracts ([side-effect-expr void?]
                      [stmt statement?])]{

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
                             (list)
                             identifier]
                    [quasi-pattern (quasi-pattern ...)
                                   (unquote pattern)
                                   symbol])
         #:contracts ([body statement?])]{

Lexically binds @racket[lv] to the value it has been unified with and
then runs @racket[body].  If @racket[lv] is never unified, it is
disjunctively force-unified with each @racket[pattern].  Each
@racket[identifier] in the pattern is also lexically bound within the
@racket[body].

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
]}


@examples[
#:eval kr-eval
(query (x)
  (project x [(cons a d) (conj (≡ a 5) (== (cdr x) 6))]))
]
