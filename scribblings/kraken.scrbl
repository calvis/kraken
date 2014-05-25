#lang scribble/manual

@(require (for-label racket/base)
          (for-label (lib "kraken/main.rkt"))
          kraken)

@title{Functional-Logical Programming in Kraken}

@defmodule[kraken #:lang]

@section{Variables}

@defform[(exists (x ...) side-effect-expr ... stmt)
         #:contracts ([side-effect-expr void?]
                      [stmt statement?])]

Introduces each @racket[x] as a new lexically-scoped (existential) logic variable, 
evaluates each @racket[side-effect-expr] and discards their result.  
Then, it adds each @racket[x] to the scope of @racket[stmt] and returns it.  

@defform[(forall (e ...) side-effect-expr ... stmt)
         #:contracts ([side-effect-expr void?]
                      [stmt statement?])]

Identical to @racket[exists] except it introduces each @racket[e] as a new 
lexically-scoped universal quantification (skolemization) variable.

@section{Operators}
Operators are the basic units that combine values, relations, and other 
operators into complex logical statements.  Each operator returns a 
@racket[statement?] that can be used as an argument to other operators, 
or @racket[run] to evaluate its logical meaning.  To see these operators
in action, skip ahead to the @secref{eval} section.

@defproc[(≡ [x value?] [v value?]) statement?]

Unifies @racket[x] with @racket[v].

@defproc[(conj [clause statement?] ...) statement?]

Performs logical conjunction over @racket[clause]s.

@defproc[(disj [clause statement?] ...) statement?]

Performs logical disjunction over @racket[clause]s.

@defproc[(==> [test statement?] [consequent statement?]) statement?]

Performs logical implication.  When @racket[test] is true, the 
@racket[consequent] must also be true.  If @racket[test] is never true 
(provably false), the entire expression is equivalent to @racket[fail].

@section[#:tag "eval"]{Evaluation}

@defproc[(run [stmt statement?] [num number? #f]) (list-of state?)]

Evaluates the logical meaning of @racket[stmt], and returns the first @racket[num] 
different possible satisfying states (or all satisfying states if no number is given).


