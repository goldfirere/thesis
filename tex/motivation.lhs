%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}
import Data.Kind ( type (*), Type )
import Prelude hiding ( zipWith, concat, product, read, replicate )
import DB hiding ( Expr, type (++), eval, (:~~:)(..), TyCon, TypeRep(..), 
                   eqTyCon, eqT, tyCon, Nil, (:>) )
import GHC.Exts ( fromString )
import qualified Data.Singletons.TH as SingTH
import qualified GHC.TypeLits as TL
import qualified Data.Singletons as Sing

read = Read

\end{code}

%endif


\chapter{Motivation}
\label{cha:motivation}

Functional programmers use dependent types in two primary ways, broadly
speaking: in order to prevent erroneous programs from being accepted, and in
order to write programs that a simply typed language cannot accept.
In this chapter, I will motivate the use of dependent types from both of
these angles. The chapter concludes with a section motivating why Haskell, in
particular, is ripe for dependent types.

As a check for accuracy in these examples and examples throughout this
dissertation, all the indented, typeset code
is type-checked against my implementation
every time the text is typeset.

The code snippets throughout this dissertation are presented on a variety of
background colors. A white background indicates code that works in GHC 7.10
and (perhaps) earlier.
A \colorbox{working}{\workingcolorname} background
highlights code that newly works in GHC~8.0 due to my implementations
of previously published papers~\cite{nokinds,visible-type-application}.
A \colorbox{notyet}{\notyetcolorname}
background indicates code that does not work verbatim in GHC~8.0,
but could still be implemented via the use of singletons~\cite{singletons} and
similar workarounds. A \colorbox{noway}{\nowaycolorname} background marks code
that does not currently work in due to bugs.
To my knowledge, there is nothing more
than engineering (and perhaps the use of singletons) to get these examples
working.

Beyond the examples presented here, the literature is accumulating a wide
variety of examples of dependently typed programming. Particularly applicable
are the examples in \citet{power-of-pi}, \citet{hasochism}, and
\citet[Chapter 8]{gundry-thesis}.

\section{Eliminating erroneous programs}

\subsection{Simple example: Length-indexed vectors}
\label{sec:length-indexed-vectors}
\label{sec:example-nats}

We start by examining length-indexed vectors. This well-worn example is still
useful, as it is easy to understand and still can show off many of the
new features of Dependent Haskell.

\subsubsection{|Vec| definition}

Here is the definition of a length-indexed vector:
\begin{working}
\begin{code}
data Nat = Zero | Succ Nat    -- first, some natural numbers
data Vec :: Type -> Nat -> Type where
  Nil   ::  Vec a !Zero
  (:>)  ::  a -> Vec a n -> Vec a (!Succ n)
infixr 5 :>
\end{code}
\end{working}
I will use ordinary numerals as elements of |Nat| in this text.\footnote{In
contrast, numerals used in types in GHC are elements of a built-in type |Nat| that uses
a more efficient binary representation. It cannot be pattern-matched against.}
The |Vec| type is parameterized by both the type of the vector elements
and the length of the vector. Thus |True :> Nil| has type |Vec Bool 1| and
|'x' :> 'y' :> 'z' :> Nil| has type |Vec Char 3|.

While |Vec| is a fairly ordinary GADT, we already see one feature newly
introduced by my work: the use of |Type| in place of |*|. Using |*| to classify
ordinary types is troublesome because |*| can also be a binary operator. 
For example, should |F * Int| be a function |F| applied to |*| and |Int|
or the function |*| applied to |F| and |Int|? In order to avoid getting caught
on this detail, Dependent Haskell introduces |Type| to classify ordinary types.
(\pref{sec:parsing-star} discusses a migration strategy from legacy Haskell
code that uses |*|.)

Another question that may come up right away is about my decision to use
|Nat|s in the index. Why not |Integer|s? In Dependent Haskell, |Integer|s
are indeed available in types. However, since we lack simple definitions for
|Integer| operations (for example, what is the body of |Integer|'s
|+| operation?), it is hard to reason about them in types. This point
is addressed more fully in \pref{sec:promoting-base-types}. For now,
it is best to stick to the simpler |Nat| type.

\subsubsection{|append|}
\label{sec:tick-promotes-functions}

Let's first write an operation that appends two vectors. We already need
to think carefully about types, because the types include information about
the vectors' lengths. In this case, if we combine a |Vec a n| and a |Vec a m|,
we had surely better get a |Vec a (n + m)|. Because we are working over
our |Nat| type, we must first define addition:

\begin{spec}
(+) :: Nat -> Nat -> Nat
Zero    + m = m
Succ n  + m = Succ (n + m)
\end{spec}
%if style == newcode
\begin{code}
instance Num Nat where
  Zero    + m = m
  Succ n  + m = Succ (n + m)

  (-) = undefined
  (*) = undefined
  negate = undefined
  abs = undefined
  signum = undefined

  fromInteger 0 = Zero
  fromInteger n = Succ (fromInteger (n-1))
\end{code}
%endif

Now that we have worked out the hard bit in the type, appending the vectors
themselves is easy:
%format !+ = "\mathop{\tick{+}}"
\begin{notyet}
\begin{spec}
append :: Vec a n -> Vec a m -> Vec a (n !+ m)
append Nil       w = w
append (a :> v)  w = a :> (append v w)
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
type family (n :: Nat) + (m :: Nat) :: Nat where
  !Zero + m = m
  !Succ n + m = !Succ (n + m)

append :: Vec a n -> Vec a m -> Vec a (n + m)
append Nil       w = w
append (a :> v)  w = a :> (append v w)
\end{code}
%endif
There is a curiosity in the type of |append|: the addition between |n|
and |m| is performed by the operation |!+|. Yet we have defined the
addition operation |+|. What's going on here?

Haskell maintains two separate namespaces: one for types and one for terms.
Doing so allows declarations like |data X = X|, where the data constructor
|X| has type |X|. With Dependent Haskell, however, terms may appear in types.
(And types may, less frequently, appear in terms; see \pref{sec:type-in-term}.)
We thus need a mechanism for telling the compiler which namespace we want.
In a construct that is syntactically a type (that is, appearing after a |::|
marker or in some other grammatical location that is ``obviously'' a type),
the default namespace is the type namespace. If a user wishes to use a term-level
definition, the term-level definition is prefixed with a |!|. Thus, |!+| simply
uses the term-level |+| in a type. Note that the |!| mark has no semantic
content---it is \emph{not} a promotion operator. It is simply a marker in the
source code to denote that the following identifier lives in the term-level
namespace.

The fact that Dependent Haskell allows us to use our old, trusty, term-level
|+| in a type is one of the two chief qualities that makes it a dependently
typed language.

\subsubsection{|replicate|}
\label{sec:replicate-example}

Let's now write a function that can create a vector of a given length with
all elements equal. Before looking at the function over vectors, we'll
start by considering a version of this function over lists:
\begin{code}
listReplicate :: Nat -> a -> [a]
listReplicate Zero      _ = []
listReplicate (Succ n)  x = x : listReplicate n x
\end{code}

With vectors, what will the return type be? It surely will mention
the element type |a|, but it also has to mention the desired length of the
list. This means that we must give a name to the |Nat| passed in. Here
is how it is written in Dependent Haskell:
\begin{notyet}
\begin{spec}
replicate :: forall a. pi (n :: Nat) -> a -> Vec a n
replicate Zero      _ = Nil
replicate (Succ n)  x = x :> replicate n x
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
$(SingTH.genSingletons [''Nat])
replicate :: SNat (n :: Nat) -> a -> Vec a n
replicate SZero _ = Nil
replicate (SSucc n) x = x :> replicate n x
\end{code}
%endif
The first argument to |replicate| is bound by |pi (n :: Nat)|. Such an
argument is available for pattern matching at runtime but is also available
in the type. We see the value |n| used in the result |Vec a n|. This is
an example of a dependent pattern match, and how this
function is well-typed is considered is some depth in \pref{sec:dependent-pattern-match}.

The ability to have an argument available for runtime pattern matching
and compile-time type checking is the other chief quality that makes
Dependent Haskell dependently typed.

\subsubsection{Invisibility in |replicate|}

The first parameter to |replicate| above is actually redundant, as it can
be inferred from the result type. We can thus write a version with this type:
\begin{notyet}
\begin{spec}
replicateInvis :: pi (n :: Nat). forall a. a -> Vec a n
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
type family U n where
  U 0 = !Zero
  U n = !Succ (U (n TL.- 1))
replicateInvis :: forall n a. SingTH.SingI n => a -> Vec a n
\end{code}
%endif
Note that the type begins with |pi (n :: Nat).| instead of
|pi (n :: Nat) ->|. The use of the .~there recalls the existing Haskell
syntax of |forall a.|, which denotes an invisible argument |a|. Invisible
arguments are omitted at function calls and definitions.
On the other hand, the |->| in |pi (n :: Nat) ->| means that the argument
is visible and must be provided at every function invocation and defining
equation.
This choice of syntax is due to \citet{gundry-thesis}.
Some readers may prefer the
terms \emph{explicit} and \emph{implicit} to describe visibility; however,
these terms are sometimes used in the literature (e.g.,~\cite{miquel-icc})
when talking about erasure
properties. I will stick to \emph{visible} and \emph{invisible} throughout this
dissertation.

We can now use type inference to work out the value of |n| that should be
used:
%if style == poly
%format (U x) = x
%endif
\begin{code}
fourTrues :: Vec Bool (U 4)
fourTrues = replicateInvis True
\end{code}

How should we implement |replicateInvis|, however? We need to use an
\emph{invisibility override}. The implementation looks like this:
\begin{notyet}
\begin{spec}
replicateInvis (at Zero)      _ = Nil
replicateInvis (at (Succ _))  x = x :> replicateInvis x
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
replicateInvis x = case (Sing.sing :: Sing.Sing n) of
  SZero -> Nil
  SSucc n -> Sing.withSingI n (replicateInvis x)
\end{code}
%endif
The $\at$ in those patterns means that we are writing an ordinarily
invisible argument visibly. This is necessary in the body of
|replicateInvis| as we need to pattern match on the choice of |n|.
An invisibility override can also be used at call sites:
|replicateInvis (at 2) 'q'| produces the vector |'q' :> 'q' :> Nil| of
type |Vec Char 2|. It is useful when we do not know the result type
of a call to |replicateInvis|.\footnote{The use of $\at$ here is a
generalization of its use in GHC 8 in visible type application~\cite{visible-type-application}.}

\subsubsection{Computing the length of a vector}

Given a vector, we would like to be able to compute its length. At first,
such an idea might seem trivial---the length is right there in the type!
However, we must be careful here. While the length is indeed in the type,
types are erased in Haskell. That length is thus not automatically
available at runtime
for computation. We have two choices for our implementation of |length|:
\begin{notyet}
\begin{spec}
lengthRel :: pi n. forall a. Vec a n -> Nat
lengthRel (at n) _ = n
\end{spec}
\end{notyet}\vspace{-3ex}
\begin{code}
lengthIrrel :: forall n a. Vec a n -> Nat
lengthIrrel Nil       = 0
lengthIrrel (_ :> v)  = 1 + lengthIrrel v
\end{code}
%if style == newcode
\begin{code}
lengthRel :: forall n a. Sing.SingI (n :: Nat) => Vec a n -> Nat
lengthRel _ = Sing.fromSing (Sing.sing :: Sing.Sing n)
\end{code}
%endif 
The difference between these two functions is whether or not they quantify
|n| relevantly. A \emph{relevant} parameter, bound by |pi|, is one available at runtime.\footnote{This is a slight simplification, as relevance still has meaning in types that
are erased. See \pref{sec:relevance}.} In |lengthRel|, the type declares that
the value of |n|, the length of the |Vec a n| is available at runtime.
Accordingly, |lengthRel| can simply return this value. The one visible
parameter, of type |Vec a n| is needed only so that type inference can infer
the value of |n|. This value must be somehow known at runtime in the calling
context, possibly because it is statically known (as in |lengthRel fourTrues|)
or because |n| is available relevantly in the calling function.

On the other hand, |lengthIrrel| does not need runtime access to |n|; the
length is computed by walking down the vector and counting the elements.
When |lengthRel| is available to be called, both |lengthRel| and |lengthIrrel|
should always return the same value. (In contrast, |lengthIrrel| is always available
to be called.)

The choice of relevant vs.~irrelevant parameter is denoted by the use of
|pi| or |forall| in the type: |lengthRel| says |pi n| while
|lengthIrrel| says |forall n|. The programmer must choose between relevant
and irrelevant quantification when writing or calling functions.
(See \pref{sec:related-type-erasure} for a discussion of how this choice
relates to decisions in other dependently typed languages.)

We see also that |lengthRel| takes |n| before |a|. Both
are invisible, but the order is important because we wish to bind the
first one in the body of |lengthRel|. If I had written |lengthRel|'s type
beginning with |forall a. pi n.|, then the body would have to be
|lengthRel (at _) (at n) _ = n|.

\subsubsection{Conclusion}

These examples have warmed us up to examine more complex uses of dependent
types in Haskell. We have seen the importance of discerning the relevance of
a parameter, invisibility overrides, and dependent pattern matching.

\subsection{A strongly typed simply typed $\lambda$-calculus interpreter}
\label{sec:stlc}

It is straightforward to write an interpreter for the simply typed
$\lambda$-calculus (STLC) in Haskell. However, how can we be sure that our
interpreter is written correctly? Using some features of dependent
types---notably, generalized algebraic datatypes, or GADTs---we can
incorporate the STLC's type discipline into our interpreter.\footnote{The skeleton of this example---using GADTs to verify the implementation of the STLC---is not novel, but I am unaware of a canonical reference for it.} Using the extra
features in Dependent Haskell, we can then write both a big-step semantics and
a small-step semantics and have GHC check that they correspond.

\subsubsection{Type definitions}

Our first step is to write a type to represent the types in our $\lambda$-calculus:
\begin{code}
data Ty = Unit | Ty :~> Ty
infixr 0 :~>
\end{code}
I choose |Unit| as our one and only base type, for simplicity. This calculus
is clearly not suitable for computation, but it demonstrates the use of GADTs
well. The model described here scales up to a more featureful
$\lambda$-calculus.\footnote{For example, see my work on \package{glambda} at
  \url{https://github.com/goldfirere/glambda}.}
The |infixr| declaration declares that the constructor |:~>| is right-associative,
as usual.

We are then confronted quickly with the decision of how to encode bound
variables. Let's choose de Bruijn indices~\cite{debruijn}, as these are well known
and conceptually simple. However, instead of using natural numbers to
represent our variables, we'll use a custom |Elem| type:
\begin{code}
data Elem :: [a] -> a -> Type where
  EZ  ::               Elem  (x !: xs)  x
  ES  :: Elem xs x ->  Elem  (y !: xs)  x
\end{code}
A value of type |Elem xs x| is a proof that |x| is in the list |xs|. This
proof naturally takes the form of a natural number, naming the place in |xs|
where |x| lives. The first constructor |EZ| is a proof that |x| is the first
element in |x !: xs|. The second constructor |ES| says that, if we know
|x| is an element in |xs|, then it is also an element in |y !: xs|.

We can now write our expression type:
\begin{code}
data Expr :: [Ty] -> Ty -> Type where
  Var  :: Elem ctx ty                              ->  Expr ctx ty
  Lam  :: Expr (arg !: ctx) res                    ->  Expr ctx (arg !:~> res)
  App  :: Expr ctx (arg !:~> res) -> Expr ctx arg  ->  Expr ctx res
  TT   ::                                              Expr ctx !Unit
\end{code}
As with |Elem list elt|, a value of type |Expr ctx ty| serves two purposes:
it records the structure of our expression, \emph{and} it proves a property,
namely that the expression is well-typed in context |ctx| with type |ty|.
Indeed, with some practice, we can read off the typing rules for the simply
typed $\lambda$-calculus direct from |Expr|'s definition. In this way, it is
impossible to create an ill-typed |Expr|.

\subsubsection{Big-step evaluator}

We now wish to write both small-step and big-step operational semantics
for our expressions. First, we'll need a way to denote values in our language:
\begin{code}
data Val :: Ty -> Type where
  LamVal  :: Expr ![arg] res ->  Val (arg !:~> res)
  TTVal   ::                     Val !Unit
\end{code}

Our big-step evaluator has a straightforward type:
\begin{code}
eval :: Expr ![] ty -> Val ty
\end{code}
This type says that a well-typed, closed expression (that is, the context
is empty) can evaluate to a well-typed value of the same type |ty|.
Only a type-preserving evaluator will have that type, so GHC can check
the type-soundness of our $\lambda$-calculus as it compiles our interpreter.

To implement |eval|, we'll need several auxiliary functions, each
with an intriguing type:
\begin{code}
-- Shift the de Bruijn indices in an expression
shift :: forall ctx ty x. Expr ctx ty -> Expr (x !: ctx) ty

-- Substitute one expression into another
subst :: forall ctx s ty. Expr ctx s -> Expr (s !: ctx) ty -> Expr ctx ty

-- Perform $\beta$-reduction
apply :: Val (arg !:~> res) -> Expr ![] arg -> Expr ![] res
\end{code}
The type of |shift| is precisely the content of a weakening lemma: that
we can add a type to a context without changing the type of a well-typed
expression. The type of |subst| is precisely the content of a substitution lemma:
that given an expression of type |s| and an expression of type |t| (typed
in a context containing a variable bound to |s|), we can substitute and
get a new expression of type |t|. The type of |apply| shows that it
does $\beta$-reduction: it takes an abstraction of type |arg !:~> res| and
an argument of type |arg|, producing a result of type |res|.

The implementations of these functions, unsurprisingly, read much like
the proof of the corresponding lemmas. We even have to ``strengthen the
induction hypothesis'' for |shift| and |subst|; 
we need an internal recursive function with extra arguments.
Here are the first few lines of |shift| and |subst|:
%if style == poly
%format ctx0
%endif
\begin{notyet}
\begin{spec}
shift = go []
  where
    go :: forall ty. pi ctx0 -> Expr (ctx0 !++ ctx) ty -> Expr (ctx0 !++ x !: ctx) ty
    go = ...

subst e = go []
  where
    go :: forall ty. pi ctx0 -> Expr (ctx0 !++ s !: ctx) ty -> Expr (ctx0 !++ ctx) ty
    go = ...
\end{spec}
\end{notyet}
%
%if style == newcode
\begin{code}
data Length :: [a] -> Type where
  LZ :: Length ![]
  LS :: Length t -> Length (h !: t)

type family a ++ b where
  ![] ++ x = x
  (x !: xs) ++ ys = x !: (xs ++ ys)
infixr 5 ++

shift = go LZ
  where
    go :: forall ctx0 ty. Length ctx0 -> Expr (ctx0 ++ ctx) ty
                                      -> Expr (ctx0 ++ x !: ctx) ty
    go l_ctx0 (Var v)     = Var (shift_elem l_ctx0 v)
    go l_ctx0 (Lam body)  = Lam (go (LS l_ctx0) body)
    go l_ctx0 (App e1 e2) = App (go l_ctx0 e1) (go l_ctx0 e2)
    go _      TT          = TT

    shift_elem :: Length ctx0 -> Elem (ctx0 ++ ctx) y
                              -> Elem (ctx0 ++ x !: ctx) y
    shift_elem LZ     e      = ES e
    shift_elem (LS _) EZ     = EZ
    shift_elem (LS l) (ES e) = ES (shift_elem l e)

subst e = go LZ
  where
    go :: forall ctx0 ty. Length ctx0 -> Expr (ctx0 ++ s !: ctx) ty
                                      -> Expr (ctx0 ++ ctx) ty
    go len (Var v)     = subst_var len v
    go len (Lam body)  = Lam (go (LS len) body)
    go len (App e1 e2) = App (go len e1) (go len e2)
    go _   TT          = TT

    subst_var :: forall ctx0 ty. Length ctx0 -> Elem (ctx0 ++ s !: ctx) ty
                                             -> Expr (ctx0 ++ ctx) ty
    subst_var LZ       EZ     = e
    subst_var LZ       (ES v) = Var v
    subst_var (LS _)   EZ     = Var EZ
    subst_var (LS len) (ES v) = shift (subst_var len v)

apply (LamVal body) arg = subst arg body
\end{code}
%endif
As many readers will be aware, to prove the weakening and substitution lemmas,
it is necessary to consider the possibility that the context change is not
happening at the beginning of the list of types, but somewhere in the middle.
This generality is needed in the |Lam| case, where we wish to use an induction
hypothesis; the typing rule for |Lam| adds the type of the argument to the
context, and thus the context change is no longer at the beginning of the
context.

Naturally, this issue comes up in our interpreter's implementation,
too. The |go| helper functions have types generalized over a possibly non-empty
context prefix, |ctx0|. This context prefix is appended to the existing
context using |!++|, the promoted form of the existing |++| list-append operator.
(Using |!| for promoting functions is a natural extension of the existing
convention of using |!| to promote constructors from terms to types; see also
\pref{sec:tick-promotes-functions}.)
The |go| functions also $\Pi$-quantify over |ctx0|, meaning that the value
of this context prefix is available in types (as we can see) and also at
runtime. This is necessary because the functions need the length of |ctx0|
at runtime, in order to know how to shift or substitute. Note also the
syntax |pi ctx0 ->|, where the $\Pi$-bound variable is followed by an |->|.
The use of an arrow here (as opposed to a |.|) indicates that the parameter
is \emph{visible} in source programs; the empty list is passed in visibly
in the invocation of |go|. (See also \pref{sec:visibility}.) The final interesting
feature of these types is that they re-quantify |ty|. This is necessary because
the recursive invocations of the functions may be at a different type than the
outer invocation. The other type variables---which do not change during recursive
calls to the |go| helper functions---are lexically bound
by the |forall| in the type signature of the outer function.

The implementation of these functions is fiddly and uninteresting, and is
omitted from this text. However, writing this implementation is made much
easier by the precise types. If I were to make a mistake in the delicate
de Bruijn shifting operation, I would learn of my mistake immediately, without
any testing. In an algorithm so easy to get wrong, this 
feedback is wonderful, indeed.

With all of these supporting functions written, the evaluator itself is
dead simple:
\begin{code}
eval (Var v)      = case v of {}  -- no variables in an empty context
eval (Lam body)   = LamVal body
eval (App e1 e2)  = eval (apply (eval e1) e2)
eval TT           = TTVal
\end{code}
The only curiosity here is the empty |case| expression in the |Var| case,
which eliminates |v| of the uninhabited type |Elem ![] ty|.

\subsubsection{Small-step stepper}
We now turn to writing the small-step semantics. We could proceed in
a very similar fashion to the big-step semantics, by defining a |step|
function that steps an expression either to another expression or to
a value. But we want better than this.

Instead, we want to ensure that the small-step semantics respects the big-step
semantics. That is, after every step, we want the value---as given by the
big-step semantics---to remain the same. We thus want the small-step stepper
to return a custom datatype, marrying the result of stepping with evidence
that the value of this result agrees with the value of the original expression:\footnote{This example fails for two reasons:
\begin{itemize}
\item It contains data constructors with constraints
occurring after visible parameters, something currently unsupported by GHC,
as GHC imposes rigid requirements on the shape of data constructor types.
These requirements will be relaxed as I implement dependent types.
\item Writing a type-level version of |shift| (automatic promotion with |!|
is not yet implemented) is not yet possible. The problem is that one of
the helper function's arguments has a type that mentions the |++| function,
something that is not yet accepted.
\end{itemize}
I do not expect either of these problems to be significant.}
\begin{noway}
\begin{spec}
data StepResult :: Expr ![] ty -> Type where
  Stepped  :: pi (e'  :: Expr ![]  ty) -> (!eval e ~ !eval e')  => StepResult e
  Value    :: pi (v   :: Val       ty) -> (!eval e ~ v)         => StepResult e
\end{spec}
\end{noway}
A |StepResult e| is the result of stepping an expression |e|. It either contains
a new expression |e'| whose value equals |e|'s value, or it contains the value
|v| that is the result of evaluating |e|.

An interesting detail about these constructors is that they feature an equality
constraint \emph{after} a runtime argument. Currently, GHC requires that all
data constructors take a sequence of type arguments, followed by constraints,
followed by regular arguments. Generalizing this form poses no
real difficulty, however.

With this in hand, the |step| function is remarkably easy to write:
\begin{noway}
\begin{spec}
step :: pi (e :: Expr ![] ty) -> StepResult e
step (Var v)      = case v of {}  -- no variables in an empty context
step (Lam body)   = Value (LamVal body)
step (App e1 e2)  = case step e1 of
  Stepped e1'  -> Stepped (App e1' e2)
  Value v      -> Stepped (apply v e2)
step TT           = Value TTVal
\end{spec}
\end{noway}
Due to GHC's ability to freely use equality assumptions, |step|
requires no explicit manipulation of equality proofs. Let's look at the |App|
case above. We first check whether or not |e1| can take a step. If it can,
we get the result of the step |e1'| \emph{and} a proof that |!eval e1 ~ !eval e1'|.
This proof enters into the type-checking context and is invisible in the program
text. On the right-hand side of the match, we conclude that |App e1 e2| steps to
|App e1' e2|. This requires a proof that |!eval (App e1 e2) ~ !eval (App e1' e2)|.
Reducing |!eval| on both sides of that equality gives us
\[
|!eval (!apply (!eval e1) e2) ~ !eval (!apply (!eval e1') e2)|.
\]
 Since we know
|!eval e1 ~ !eval e1'|, however, this equality is easily solvable; GHC does the
heavy lifting for us. Similar reasoning proves the equality in the second branch
of the |case|, and the other clauses of |step| are straightforward.

The ease with which these equalities are solved is unique to Haskell. I have
translated this example to Coq, Agda, and Idris; each has its shortcomings:
\begin{itemize}
\item Coq deals quite poorly with indexed types, such as |Expr|. The problem appears
to stem from Coq's weak support for dependent pattern matching. For example, if we
inspect a |ctx| to discover that it is empty, Coq, by default, forgets the
equality |ctx = []|. It then, naturally, fails to use the equality to rewrite
the types of the right-hand sides of the pattern match. This can be overcome through
various tricks, but it is far from easy. Alternatively,
Coq's relatively new \keyword{Program} construct helps with this burden
somewhat but still does not always work as smoothly as GADT pattern 
matching in Haskell.
Furthermore, even once the challenges around indexed types
are surmounted, it is necessary to prove that |eval| terminates---a non-trivial
task---for Coq to
accept the function.

\item Agda does a better job with indexed types, but it is not designed around
implicit proof search. A key part of Haskell's elegance in this example is that
pattern-matching on a |StepResult| reveals an equality proof to the type-checker,
and this proof is then used to rewrite types in the body of the pattern match. This
all happens without any direction from the programmer. In Agda,
the equality proofs must be unpacked and used with Agda's \keyword{rewrite} tactic.

Like Coq, Agda normally requires that functions terminate. However, we can
easily disable the termination checker: use
@{-# NO_TERMINATION_CHECK #-}@.

%{
%format assert_total = "\keyword{assert\_total}"
\item Like Agda, Idris
works well with indexed types. The |eval| function is, unsurprisingly, inferred
to be partial, but this is easy enough to fix with a well-placed
|assert_total|. However, Idris's proof search mechanism is unable
to find proofs that |step| is correct in the |App| cases. (Using an \keyword{auto}
variable, Idris is able to find the proofs automatically in the other |step|
clauses.) Idris comes the closest to Haskell's brevity in this example, but
it still requires two places where equality proofs must
be explicitly manipulated.
%}
\end{itemize}

\subsubsection{Conclusion}

We have built up a small-step stepper whose behavior is verified against a
big-step evaluator. Despite this extra checking, the |step| function will run
in an identical manner to one that is unchecked---there is no runtime effect
of the extra verification. We can be sure of this because we can audit the
types involved and see that only the expression itself is around at runtime;
the rest of the arguments (the indices and the equality proofs) are erased.
Furthermore, getting this all done is easier and more straightforward in
Dependent Haskell than in the other three dependently typed languages I
tried. Key to the ease of encoding in Haskell is that Haskell does not worry
about termination (see \pref{sec:no-termination-check}) and
has an aggressive rewriting engine used to solve equality predicates.

%% To pull this off, we will need a dependent pair, or $\Sigma$-type:
%% %format :&: = "\mathop{{:}{\&}{:}}"
%% \begin{notyet}
%% \begin{spec}
%% data Sigma (s :: Type) (t :: s -> Type) where
%%   (:&:) :: pi (fst :: s) -> t fst -> Sigma s t

%% proj1 :: Sigma s t -> s
%% proj1 (a :&: _) = a

%% proj2 :: pi (sig :: Sigma s t) -> t (!proj1 sig)
%% proj2 (_ :&: b) = b
%% \end{spec}
%% \end{notyet}
%% A $\Sigma$-type |Sigma s t| is similar to an ordinary pair |(s, t)| except
%% that the type |t| is a function that depends on the chosen value of the first
%% element, called |fst| above. Note that |fst| is $\Pi$-quantified, making it
%% available both in types and at runtime. In our case, here is the type we will
%% want to use for |t|:
%% %
%% \begin{noway}
%% \begin{spec}
%% data SameValue (e1 :: Expr ![] ty) (e2 :: Expr ![] ty) where
%%   SameValue :: (!eval e1 ~ !eval e2) => SameValue e1 e2
%% \end{spec}
%% \end{noway}
%% %
%% Putting all of this together, here is the type we get for |step|:
%% \begin{noway}
%% \begin{spec}
%% step :: pi (e :: Expr ![] ty) -> Either  (Sigma (Expr  ![]  ty) (SameValue e))
%%                                          (Sigma (Val        ty) ((:~:) (!eval e)))
%% \end{spec}
%% \end{noway}
%% This says that, for every closed expression |e| of type |ty|, we can either
%% produce another expression of type |ty| such that the new expression has the
%% same value as the original one, or we produce a value of type |ty| that
%% is indeed the value of the original expression.

%% This function is remarkably easy to implement:

\subsection{Type-safe database access with an inferred schema}
\label{sec:dependent-db-example}

Many applications need to work in the context of some external database.
Haskellers naturally want their interface to the database to be well-typed,
and there already exist libraries that use (non-dependent) Haskell's fancy
types to good effect for database access. (See \package{opaleye}\footnote{\url{https://github.com/tomjaguarpaw/haskell-opaleye}} for an advanced, actively
developed and actively used example of such a library.) Dependent Haskell
allows us to go one step further and use type inference to infer
a database schema from the database access code.

This example is inspired by the third example by \citet{power-of-pi};
the full code powering the example is available online.\footnote{\url{https://github.com/goldfirere/dependent-db}}

\begin{figure}
\begin{center}
The @students@ table: \\[1ex]
\begin{tabular}{llcc}
@last@ & @first@ & @id@ & @gradyear@ \\ \hline
|"Matthews"| &
|"Maya"| &
1 &
2018 \\ 
|"Morley"| &
|"Aimee"| &
2 &
2017 \\
|"Barnett"| &
|"William"| & 
3 & 
2020 \\ 
|"Leonard"| &
|"Sienna"| &
4 & 
2019 \\ 
|"Oliveira"| &
|"Pedro"| & 
5 &
2017 \\ 
|"Peng"| & 
|"Qi"| & 
6 & 
2020 \\ 
|"Chakraborty"| & 
|"Sangeeta"| & 
7 &
2018 \\ 
|"Yang"| & 
|"Rebecca"| & 
8 &
2019
\end{tabular} \\[2ex]
The @classes@ table: \\[1ex]
\begin{tabular}{lll}
@name@ & @students@ & @course@ \\ \hline
|"Blank"| &
[2,3,7,8] &
|"Robotics"| \\
|"Eisenberg"| &
[1,2,5,8] &
|"Programming Languages"| \\
|"Kumar"| & 
[3,6,7,8] & 
|"Artificial Intelligence"| \\
|"Xu"| &
[1,3,4,5] &
|"Graphics"| \\ 
\end{tabular}
\end{center}
\caption{Database tables used in \pref{sec:dependent-db-example}.}
\label{fig:db-example}
\end{figure}

Instead of starting with the library design, let's start with a concrete
use case. Suppose we are writing an information system for a university.
The current task is to write a function that, given the name of a professor,
prints out the names of students in that professor's classes. There are
two database tables of interest, exemplified in \pref{fig:db-example}.
Our program will retrieve a professor's record and then look up the students
by their ID number.

Our goal in this example is understanding the broad strokes of how the
database library works and what it is capable of, not all the precise details.
If you wish to understand more, please check out the full source code online.

\subsubsection{Accessing the database}

\begin{figure}
\begin{working}
\begin{code}
type NameSchema = [ Col "first" String, Col "last" String ]

printName :: Row NameSchema -> IO ()
printName (first ::> last ::> _) = putStrLn (first ++ " " ++ last)

queryDB classes_sch students_sch = do
  classes_tab   <- loadTable "classes.table"   classes_sch
  students_tab  <- loadTable "students.table"  students_sch

  putStr "Whose students do you want to see? "
  prof <- getLine

  let  joined 
         =  project $
            select (field (at "id") (at Int) `elementOf` field (at "students")) $
            product  (select  (field (at "prof") === literal prof)
                              (read classes_tab))
                     (read students_tab)
  rows <- query joined
  mapM_ printName rows
\end{code}
\end{working}
\caption{The |queryDB| function}
\label{fig:queryDB}
\end{figure}

The main worker function that retrieves and processes the information of interest
from the database is |queryDB|, in \pref{fig:queryDB}.
Note that this function is not assigned a type
signature; we'll return to this interesting point in
\pref{sec:inferring-schema}. The |queryDB| function takes in the schemas for the two tables
it will retrieve the data from. It loads the tables that correspond
to the schemas; the |loadTable| function makes sure that the table (as specified
by its filename) does
indeed correspond to the schema. An I/O interaction with the user then
ensues, resulting in a variable |prof| of type |String| containing the
desired professor's name.

\begin{figure}
\begin{notyet}
\begin{spec}
data Column = Col String Type
type Schema = [Column]

data Table  ::  Schema -> Type  -- a table according to a schema
data RA     ::  Schema -> Type  -- a |R|elational |A|lgebra
data Expr   ::  Schema -> Type -> Type  -- an expression

loadTable  ::  String -> pi (s :: Schema) -> IO (Table s)

project    ::  Subset s' s => RA s -> RA s'
select     ::  Expr s Bool -> RA s -> RA s
field      ::  forall name ty s. In name ty s => Expr s ty
elementOf  ::  Eq ty => Expr s ty -> Expr s [ty] -> Expr s Bool
product    ::  !disjoint s s' ~ !True => RA s -> RA s -> RA (s !++ s')
literal    ::  ty -> Expr s ty
read       ::  Table s -> RA s
\end{spec}
\end{notyet}
\caption{Types used in the example of \pref{sec:dependent-db-example}.}
\label{fig:query-types}
\end{figure}

The |joined| variable then gets assigned to a large query against the database.
This query:
\begin{enumerate}
\item reads in the @classes@ table,
\item selects out any rows that mention the desired |prof|,
\item computes the Cartesian product of these rows and all the rows in the @students@ table,
\item selects out those rows where the @id@ field is in the @students@ list,
\item and finally projects out the name of the student.
\end{enumerate}
The types of the components of this query are in \pref{fig:query-types}.
There are a few points of interest in looking at this code:
\begin{itemize}
\item The query is well-typed by construction. Note the intricate types
appearing in \pref{fig:query-types}. For example, |select| takes an expression
used to select which rows of a table are preserved. This operation naturally
requires an |Expr s Bool|, where |s| is the schema of interest and the
|Bool| indicates that we have a Boolean expression (as opposed to one that
results in a number, say). The |RA| type does not permit ill-typed queries,
such as taking the Cartesian product of two tables with overlapping column
names (see the type of |product|), as projections from such a combination
would be ambiguous.
\item Use of |field| requires the $\at$ invisibility override marker, as
we wish to specify the name of the field.
\item In the first |select| expression, we must specify the type of the
field as well as the name, whereas in the second |select| expression, we
can omit the type. In the second case, the type can be inferred by comparison
with the literal |prof|. In the first, type inference tells us that @id@ is
the element type of @students@, but we need to be more concrete than this---hence
the |(at Int)| passed to |field|.
\item The use of |project| at the top projects out the first and last name
of the student, even though neither @first@ nor @last@ is mentioned there.
Type inference does the work for us, as we pass the result of running the
query to |printName|, which has a type signature that states it works over
only names.
\end{itemize}

\subsubsection{Inferring a schema}
\label{sec:inferring-schema}
\label{sec:type-in-term}
\label{sec:th-quote}

Type inference works to infer the type of |queryDB|, assigning it this
whopper:
\begin{notyet}
\begin{spec}
ghci> :type queryDB
queryDB
  ::  pi (s :: Schema) (s' :: Schema)
  ->  (  !disjoint s s' ~ !True, In "students" [Int] (s !++ s'),
         In "prof" String s, In "last" [Char] (s !++ s'),
         In "id" Int (s !++ s'), In "first" [Char] (s !++ s') )
  =>  IO ()
\end{spec}
\end{notyet}
The cavalcade of constraints are all inferred from the query above
quite straightforwardly.\footnote{What may be more surprising to the
skeptical reader is that a $\Pi$-type is inferred, especially if you
have already read \pref{cha:type-inference}. However, I maintain that
the \bake/ algorithm in \pref{cha:type-inference} infers this type.
The two parameters to |queryDB| are clearly |Schema|s, and the body
of |queryDB| asserts constraints on these |Schema|s. Note that the
type inference algorithm infers only relevant, visible parameters, but
these arguments are indeed relevant and visible. The dependency comes
in after solving, when the quantification telescope $\Delta$ output
by the solver has constraints depend on a visible argument.

As further justification for stating that \bake/ infers this type,
GHC infers a type quite like this today, albeit using singletons. The
appearance of singletons in the type inferred today is why this snippet
is presented on a \notyetcolorname{} background.}
But how can we call |queryDB| satisfying all of these constraints?

The call to |queryDB| appears here:
%if style == newcode
\begin{code}
$(return [])
main  :: IO ()
main  =  withSchema "classes.schema"   $ \ classes_sch ->
         withSchema "students.schema"  $ \ students_sch ->
         $(checkSchema !queryDB [!classes_sch, !students_sch])
\end{code}
%endif
\begin{notyet}
\begin{spec}
main  :: IO ()
main  =  do  classes_sch   <- loadSchema "classes.schema"
             students_sch  <- loadSchema "students.schema"
             $(checkSchema !queryDB [!classes_sch, !students_sch])
\end{spec}
\end{notyet}
The two calls to |loadSchema| are uninteresting. The third line of |main|
is a Template Haskell~\cite{template-haskell} splice. Template Haskell is
GHC's metaprogramming facility. The quotes we see before the arguments to
|checkSchema| are Template Haskell quotes, not the promotion |!| mark we
have seen so much.

The function |checkSchema :: Name -> [Name] -> Q Exp| takes the name of
a function (|queryDB|, in our case), names of schemas to be passed to
the function (|classes_sch| and |students_sch|) and produces
some Haskell code that arranges for an appropriate function call.
(|Exp| is the Template Haskell type containing a Haskell expression, and
|Q| is the name of the monad Template Haskell operates under.) In order
to produce the right function call to |queryDB|,
|checkSchema| queries for the inferred type of |queryDB|. It then examines
this type and extracts out all of the constraints on the schemas.
In the produced Haskell expression, |checkSchema| arranges for calls
to several functions that establish the constraints before calling |queryDB|.
To be concrete, here is the result of the splice; the following
code is spliced into the |main| function in place of the call to |checkSchema|:
%
\begin{notyet}
\begin{spec}
checkDisjoint classes_sch students_sch                          $
checkIn "students" ^^  ^[^Int]   (classes_sch ++ students_sch)  $
checkIn "prof" ^^      ^String   classes_sch                    $
checkIn "last" ^^      ^[^Char]  (classes_sch ++ students_sch)  $
checkIn "id" ^^        ^Int      (classes_sch ++ students_sch)  $
checkIn "first" ^^     ^[^Char]  (classes_sch ++ students_sch)  $
queryDB classes_sch students_sch
\end{spec}
\end{notyet}
Before discussing |checkDisjoint| and |checkIn|, I must explain a new
piece of syntax: just as |!| allows us to use a term-level name in a type,
the new syntax |^| allows us to use a type-level name in a term. That is
all the syntax does. For example |^[^Int]| is the list type constructor
applied to the type |Int|, not a one-element list (as it would otherwise
appear).

The |checkDisjoint| and |checkIn| functions establish the constraints
necessary to call |queryDB|. Here are their types:

\begin{notyet}
\begin{spec}
checkDisjoint  ::  pi (sch1 :: Schema) (sch2 :: Schema)
               ->  ((!disjoint sch1 sch2 ~ !True) => r)
               ->  r
checkIn        ::  pi (name :: String) (ty :: Type) (schema :: Schema)
               ->  (In name ty schema => r)
               ->  r
\end{spec}
\end{notyet}
Both functions take input information\footnote{Readers might be alarmed
to see here a |Type| being passed at runtime. After all, a key feature
of Dependent Haskell is type erasure! However, passing types at runtime
is sometimes necessary, and using the type |Type| to do so is a natural
extension of what is done today. Indeed, today's |TypeRep| (explored in
detail by \citet{typerep}) is essentially a singleton for |Type|. As
Dependent Haskell removes other singletons, so too will it remove |TypeRep|
in favor of dependent pattern matching on |Type|. As with other aspects
of type erasure, users will choose which types to erase by the choice
between |pi|-quantification and a |forall|-quantification.}
to validate and a continuation
to call if indeed the input is valid. In this implementation, both functions
simply error (that is, return $\bot$) if the input is not valid, though
it would not be hard to report an error in a suitable monad.

\subsubsection{Checking inclusion in a schema}

It is instructive to look at the implementation of |checkIn|:
\begin{notyet}
\begin{spec}
checkIn  ::  pi (name :: String) (ty :: Type) (schema :: Schema)
         ->  (In name ty schema => r)
         ->  r
checkIn name _  [] _
  =  error ("Field " ++ show name ++ " not found.")
checkIn name ty (Col name' ty' : rest) k
  =  case (name `eq` name', ty `eq` ty') of
      (Just Refl,  Just Refl)  -> k
      (Just _,     _)          -> error (  "Found " ++ show name ++
                                           " but it maps to " ++ show ty')
      _                        -> checkIn name ty rest k
\end{spec}
\end{notyet}
This function searches through the |Schema| (which, recall, is just a
|[Column]|) for the desired name and type. If the search fails or the
search find the column associated with the wrong type, |checkIn| fails.
Otherwise, it will eventually call |k|, the continuation that can now
assume |In name ty schema|. The constraint |In| is implemented as a class
with instances that prove that the |(name, ty)| pair is indeed in |schema|
whenever |In name ty schema| holds.

The |checkIn| function makes critical use of a new function |eq|:\footnote{I present |eq| here as a member of the ubiquitous |Eq| class, as a definition for |eq|
should be writable whenever a definition for |==| is. (Indeed, |==| could
be implemented in terms of |eq|.) I do not, however, expect that |eq| will
end up living directly in the |Eq| class, as I doubt the Haskell community
will permit Dependent Haskell to alter such a fundamental class. Nevertheless,
the functionality sported by |eq| will be a common need in Dependent Haskell
code, and we will need to find a suitable home for the function.}
\begin{notyet}
\begin{spec}
class Eq a where
  ...
  eq :: pi (x :: a) (y :: a) -> Maybe (x :~: y)
\end{spec}
\end{notyet}
This is just a more informative version of the standard equality operator
|==|. When two values are |eq|, we can get a proof of their equality.
This is necessary in |checkIn|, where assuming this equality is necessary
in order to establish the |In| constraint before calling the
constrained continuation |k|.

\subsubsection{Conclusion}

This example has highlighted several aspects of Dependent Haskell:

\begin{itemize}
\item Writing a well-typed database access is well within the reach of
Dependent Haskell. Indeed, much of the work has already been done in
released libraries.
\item Inferring the type of |queryDB| is a capability unique to Dependent
Haskell among dependently typed languages. Other dependently
typed languages require type signatures on all top-level functions;
this example makes critical use of Haskell's ability to infer a type
in deriving the type for |queryDB|.
\item Having dependent types in a large language like Haskell sometimes
shows synergies with other aspects of the language. In this example, we
used Template Haskell to complement our dependent types to achieve something
neither one could do alone: Template Haskell's ability to inspect an inferred
type allowed us to synthesize the runtime checks necessary to prove that
a call to |queryDB| was indeed safe.
\end{itemize}

%% \subsection{Units-of-measure}

%% Just as it is easy to make a type error when programming in an untyped
%% language, it is also easy to make an error around dimensions or units
%% when doing calculations over physical quantities. Accordingly, it is
%% helpful when a type system is able to check for correct use of
%% dimensions and units. I am far from the first to suggest or implement
%% this idea, which dates back at least as far as \citet{kennedy-thesis}.
%% Checking for units in code is integrated into F#'s type system,
%% and several Haskell libraries exist (including my own) to check units.\footnote{The \package{dimensional} by Buckwalter and my \package{units} package~\cite{closed-type-families-extended,type-checking-units} are the leading examples.}
%% Recent work by Gundry also adds to the field of work integrating unit-checking
%% with Haskell~\cite{type-checker-plugins}~\cite[Chapter 3]{gundry-thesis}.

%% What new light can this well-studied area shed on our understanding of
%% Dependent Haskell?

%% \begin{itemize}
%% \item Despite the lack of full-spectrum dependent types, Haskellers try to
%% leverage their type system to do the sort of checking that generally requires
%% either dependent types or a built-in facility (as in F#).
%% \item While encoding
%% some amount of unit checking in non-dependent Haskell is possible, it is
%% painful and brittle. The \package{dimensional} approach is restricted to
%% work only with multiples of the seven base SI units

\subsection{Machine-checked sorting algorithms}

Using dependent types to check a sorting algorithm is well explored in the
literature (e.g., \cite{why-dependent-types-matter,keeping-neighbours-in-order}).
These algorithms can also be translated into Haskell, as shown in my prior
work~\cite{singletons,nyc-hug-2014}. I will thus not go into any detail
in the implementation here.

At the bottom of one implementation\footnote{\url{https://github.com/goldfirere/nyc-hug-oct2014/blob/master/OrdList.hs}} appears this function definition:
\[
|mergeSort :: [Integer] -> [Integer]|.
\]
 Note that the type of the function
is completely ordinary---there is no hint of the rich types that lurk beneath,
in its implementation. It is this fact that makes machine-checked algorithms,
such as sorting, interesting in the context of Haskell.

A Haskell programming
team may make a large application with little use for fancy types. Over time,
the team notice bugs frequently appearing in a gnarly section of code
(like a sorting algorithm, or more realistically, perhaps, an implementation
of a cryptographic primitive), and they
decide that they want extra assurances that the algorithm is correct.
That one algorithm---and no other part of the large application---might be
rewritten to use dependent types. Indeed any of the examples considered in this
chapter can be hidden beneath simply typed interfaces and thus form
just one component of a larger, \emph{simply} typed application.

\section{Encoding hard-to-type programs}

\subsection{Variable-arity |zipWith|}

The |Data.List| Haskell standard library comes with the following functions:
\begin{spec}
map       ::  (a -> b) -> [a] -> [b]
zipWith   ::  (a -> b -> c) -> [a] -> [b] -> [c]
zipWith3  ::  (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
zipWith4  ::  (a -> b -> c -> d -> e) -> [a] -> [b] -> [c] -> [d] -> [e]
...
\end{spec}
Let's pretend to rename |map| to |zipWith1| and |zipWith| to |zipWith2|.
This sequence continues up to |zipWith7|. The fact that these are different
functions means that the user must choose which one to use, based on the
arity of the function to be mapped over the lists. However, forcing the
user to choose this is a bit silly: the type system should be able to
discern which |zipWith| is correct based on the type of the function.
Dependent Haskell gives us the power to write such a variable-arity
|zipWith| function.\footnote{This example is adapted from my prior
work~\cite{closed-type-families-extended}.}

Let's build up our solution one step at a time. We'll first focus
on building a |zipWith| that is told what arity to be; then we'll
worry about inferring this arity.

Recall the definition of natural numbers from \pref{sec:example-nats}:
\begin{spec}
data Nat = Zero | Succ Nat
\end{spec}

What will the type of our final |zipWith| be? It will first take a function
and then several lists. The types of these lists are determined by the type
of the function passed in. For example, suppose our function |f| has type
|Int -> Bool -> Double|, then the type of |zipWith| should be
|(Int -> Bool -> Double) -> [Int] -> [Bool] -> [Double]|. Thus, we wish
to take the type of the function and apply the list type constructor |[]|
to each component of it.

Before we write the code for this operation, we pause to note an ambiguity
in this definition. Both of the following are sensible concrete types for a |zipWith|
over the function |f|:
%
\begin{spec}
zipWith  ::  (Int   ->  Bool    ->  Double)
         ->  [Int]  ->  [Bool   ->  Double]
zipWith  ::  (Int   ->  Bool    ->  Double)
         ->  [Int]  ->  [Bool]  ->  [Double]
\end{spec}
%
The first of these is essentially |map|; the second is the classic function
|zipWith| that expects two lists. Thus, we must pass in the desired number
of parameters to apply the list type constructor to. 
The function to apply these list constructors is named
|Listify|:
%
\begin{code}
type family Listify (n :: Nat) arrows where
  Listify !Zero      a         = [a]
  Listify (!Succ n)  (a -> b)  = [a] -> Listify n b
\end{code}

We now need to create some runtime evidence of our choice for the number
of arguments.
This will be used to control the runtime operation of |zipWith|---after
all, our function must have both the correct behavior and the correct type.
We use a GADT |NumArgs| that plays two roles: it controls the runtime behavior
as just described, and it also is used as evidence to the type checker that
the number argument to |Listify| is appropriate. After all, we do not want
to call |Listify 2 (Int -> Bool)|, as that would be stuck. By pattern-matching
on the |NumArgs| GADT, we get enough information to allow |Listify| to fully
reduce.
\begin{code}
data NumArgs :: Nat -> Type -> Type where
  NAZero  :: forall a.                               NumArgs  !Zero      a
  NASucc  :: forall a b (n :: Nat). NumArgs n b  ->  NumArgs  (!Succ n)  (a -> b)
\end{code}

We now write the runtime workhorse |listApply|, with the following type:
\begin{code}
listApply :: NumArgs n a -> [a] -> Listify n a
\end{code}
The first argument is the encoding of the number of arguments to the function.
The second argument is a \emph{list} of functions to apply to corresponding
elements of the lists passed in after the second argument. Why do we need 
a list of functions? Consider evaluating |zipWith (+) [1,2] [3,4]|, where
we recur not only on the elements in the list, but on the number of arguments.
After processing the first list, we have to be able to apply different functions
to each of the elements of the second list. To wit, we need to apply the functions
|[(1 +), (2 +)]| to corresponding elements in the list |[3,4]|. (Here, we are
using Haskell's ``section'' notation for partially-applied operators.)

Here is the definition of |listApply|:
\begin{code}
listApply  NAZero       fs = fs
listApply  (NASucc na)  fs =
  \args -> listApply na (apply fs args)
  where  apply :: [a -> b] -> [a] -> [b]
         apply  (f:fs)  (x:xs)  = (f x : apply fs xs)
         apply  _       _       = []
\end{code}
It first pattern-matches on its first argument. In the |NAZero| case, each member of the list
of functions passed in has 0 arguments, so we just return the list. In the
|NASucc| case, we process one more argument (|args|), apply the list of
functions |fs| respectively to the elements of |args|, and then recur. Note
how the GADT pattern matching is essential for this to type-check---the type
checker gets just enough information for |Listify| to reduce enough so that
the second case can expect one more argument than the first case.

\paragraph{Inferring arity}
In order to infer the arity, we need to have a function that counts
up the number of arrows in a function type:
\begin{code}
type family CountArgs (f :: Type) :: Nat where
  CountArgs (a -> b)  = !Succ (CountArgs b)
  CountArgs result    = !Zero
\end{code}
The ability to write this function is unique to Haskell,
where pattern-matching on proper types (of kind |Type|) is allowed.

We need to connect this type-level function with the term-level
GADT |NumArgs|. We use Haskell's method for reflecting type-level
decisions on the term level: type classes. The following definition
essentially repeats the definition of |NumArgs|, but because this
is a definition for a class, the instance is inferred rather than
given explicitly:
\begin{code}
class CNumArgs (numArgs :: Nat) (arrows :: Type) where
  getNA :: NumArgs numArgs arrows
instance CNumArgs !Zero a where
  getNA = NAZero
instance  CNumArgs n b =>
          CNumArgs (!Succ n) (a -> b) where
  getNA = NASucc getNA
\end{code}
Note that the instances do \emph{not} overlap; they are distinguished
by their first parameter.

It is now straightforward to give the final definition of |zipWith|,
using the extension \ext{ScopedTypeVariables} to give the body
of |zipWith| access to the type variable |f|:
\begin{code}
zipWith  ::  forall f. CNumArgs (CountArgs f) f
         =>  f -> Listify (CountArgs f) f
zipWith fun
  = listApply (getNA :: NumArgs (CountArgs f) f) (repeat fun)
\end{code}
The standard Haskell function |repeat| creates an infinite list of its one
argument.

The following examples show that |zipWith| indeed infers the arity:
%if style == poly
%format example1
%format example2
%format example3
%endif
\begin{code}
example1 = zipWith (&&) [False, True, False] [True, True, False]
example2 = zipWith ((+) :: Int -> Int -> Int) [1,2,3] [4,5,6]

concat :: Int -> Char -> Double -> String
concat a b c = (show a) ++ (show b) ++ (show c)
example3 = zipWith concat  [1,2,3] ['a','b','c']
                           [3.14, 2.1728, 1.01001]
\end{code}
In |example2|, we must specify the concrete instantiation of |(+)|. In Haskell,
built-in numerical operations are generalized over a type class |Num|. In this case,
the operator |(+)| has the type |Num a => a -> a -> a|. Because it is theoretically
possible (though deeply strange!) for |a| to be instantiated with a function type,
using |(+)| without an explicit type will not work---there is no way to infer an
unambiguous arity. Specifically, |CountArgs| gets stuck. |CountArgs (a -> a -> a)|
simplifies to |Succ (Succ (CountArgs a))| but can go no further; |CountArgs a| will
not simplify to |Zero|, because |a| is not apart from |b -> c|.

\subsection{Typed reflection}
\label{sec:example-reflection}

\emph{Reflection} is the act of reasoning about a programming language from
within programs written in that language.\footnote{Many passages in this
  example are expanded upon in my prior work~\cite{typerep}.} In
Haskell, we are naturally concerned with reflecting the rich language
of Haskell types. A
reflection facility such as the one described here will be immediately
applicable in the context of Cloud Haskell. Cloud Haskell~\cite{cloud-haskell}
is an ongoing project, aiming to support writing a Haskell program that can
operate on several machines in parallel, communicating over a network. To
achieve this goal, we need a way of communicating data of all types over a
wire---in other words, we need dynamic types. On the receiving end, we would
like to be able to inspect a dynamically typed datum, figure out its type, and
then use it at the encoded type. For more information about how kind
equalities fit into Cloud Haskell, please see the GHC wiki at
\url{https://ghc.haskell.org/trac/ghc/wiki/DistributedHaskell}.

Reflection of this sort has been possible for some
time using the |Typeable| mechanism~\cite{syb}. However, the lack of kind
equalities---the ability to learn about a type's kind via pattern matching---has
hindered some of the usefulness of Haskell's reflection facility.
In this section, we explore how this is the case and how the problem is fixed.

\subsubsection{Heterogeneous propositional equality}

Kind equalities allow for the definition of
\emph{heterogeneous propositional equality}, a natural extension to the
propositional equality described in \pref{sec:prop-equality}:
%if style == poly
%format k1
%format k2
%endif
\begin{working}
\begin{code}
data (a :: k1) :~~: (b :: k2) where
  HRefl :: a :~~: a
\end{code}
\end{working}
Pattern-matching on a value of type |a :~~: b| to get |HRefl|, where |a :: k1|
and |b :: k2|, tells us both that |k1 ~ k2| and that |a ~ b|. As we'll see below,
this more powerful form of equality is essential in building the typed reflection
facility we want.

\subsubsection{Type representation}

Here is our desired representation:\footnote{This representation works well
  with an open world assumption, where users may introduce new type constants
  in any module. See my prior work~\cite[Section 4]{typerep} for more
  discussion on this point.}
%
\begin{code}
data TyCon (a :: k)
  -- abstract; the type |Int| is represented by the one value of type |TyCon Int|
data TypeRep (a :: k) where
  TyCon  :: TyCon a -> TypeRep a
  TyApp  :: TypeRep a -> TypeRep b -> TypeRep (a b)
\end{code}
%
The intent is that, for every new type declared, the compiler would supply an appropriate value of
the |TyCon| datatype. The type representation library would supply also the
following function, which computes equality over |TyCon|s, returning the
heterogeneous equality witness:
%
\begin{working}
\begin{code}
eqTyCon ::  forall (a :: k1) (b :: k2).
            TyCon a -> TyCon b -> Maybe (a :~~: b)
\end{code}
\end{working}
%if style == newcode
\begin{code}
eqTyCon = undefined
tyCon :: TyCon a
tyCon = undefined
\end{code}
%endif
%
It is critical that this function returns |(:~~:)|, not |(:~:)|. This is
because |TyCon|s exist at many different kinds. For example, |Int| is at
kind |Type|, and |Maybe| is at kind |Type -> Type|. Thus, when comparing two
|TyCon| representations for equality, we want to learn whether the types
\emph{and the kinds} are equal. If we used |(:~:)| here, then the |eqTyCon|
could be used only when we know, from some other source, that the kinds
are equal.

We can now easily write an equality test over these type representations:
%
\begin{working}
\begin{code}
eqT ::  forall (a :: k1) (b :: k2).
        TypeRep a -> TypeRep b -> Maybe (a :~~: b)
eqT (TyCon t1)     (TyCon t2)     = eqTyCon t1 t2
eqT (TyApp a1 b1)  (TyApp a2 b2)  ^^
  |  Just HRefl <- eqT a1 a2
  ,  Just HRefl <- eqT b1 b2      = Just HRefl
eqT _              _              = Nothing
\end{code}
\end{working}

Note the extra power we get by returning |Maybe (a :~~: b)| instead of just
a |Bool|. When the types are indeed equal, we get evidence that GHC can use to
be aware of this type equality during type checking. A simple return type of
|Bool| would not give the type-checker any information.

\subsubsection{Dynamic typing}

Now that we have a type representation with computable equality, we
can package that representation with a chunk of data, and so form a
dynamically typed package:
%
\begin{code}
data Dyn where
  Dyn :: forall (a :: Type). TypeRep a -> a -> Dyn
\end{code}

The |a| type variable there is an \emph{existential} type variable. We can
think of this type as being part of the data payload of the |Dyn| constructor;
it is chosen at construction time and unpacked at pattern-match time.
Because of the |TypeRep a| argument, we can learn more about |a| after
unpacking. (Without the |TypeRep a| or some other type-level information
about |a|, the unpacking code must treat |a| as an
unknown type and must be parametric in the choice of |a|.)

Using |Dyn|, we can pack up arbitrary
data along with its type and push that data across a network. The receiving
program can then make use of the data, without needing to subvert Haskell's
type system. This type representation library must be trusted to recreate
the |TypeRep| on the far end of the wire, but the equality tests above
and other functions below can live outside the trusted code base.

Suppose we were to send an
object with a function type, say |Bool -> Int| over the network. For the time
being, let's ignore the complexities of actually serializing a function---there
is a solution to that
problem\footnote{\url{https://ghc.haskell.org/trac/ghc/wiki/StaticPointers}},
but here we are concerned only with the types. We would want to apply the
received function to some argument. What we want is this:
%
\begin{code}
dynApply :: Dyn -> Dyn -> Maybe Dyn
\end{code}
%
The function |dynApply| applies its first argument to the second, as long as the
types line up. The definition of this function is fairly straightforward:
%
\begin{working}
\begin{code}
dynApply  (Dyn  (TyApp
                  (TyApp (TyCon tarrow) targ)
                  tres)
                fun)
          (Dyn targ' arg)
  |  Just HRefl <- eqTyCon tarrow (tyCon :: TyCon (->))
  ,  Just HRefl <- eqT targ targ'
  =  Just (Dyn tres (fun arg))
dynApply _ _ = Nothing
\end{code}
\end{working}
%
We first match against the expected type structure---the first |Dyn| argument
must be a function type. We then confirm that the |TyCon| |tarrow| is indeed
the representation for |(->)| (the construct |tyCon :: TyCon (->)| retrieves
the compiler-generated representation for |(->)|) and that the actual
argument type matches the expected argument type. If everything is good so
far, we succeed, applying the function in |fun arg|.

\subsubsection{Conclusion}

Heterogeneous equality is necessary throughout this example. It first is
necessary in the definition of |eqT|. In the |TyApp| case, we compare |a1|
to |a2|. If we had only homogeneous equality, it would be necessary that
the types represented by |a1| and |a2| be of the same kind. Yet, we can't
know this here! Even if the types represented by |TyApp a1 b1| and
|TyApp a2 b2| have the same kind, it is possible that |a1| and |a2| would
not. (For example, maybe the type represented by |a1| has kind |Type -> Type|
and the type represented by |a2| has kind |Bool -> Type|.) With only
homogeneous equality, we cannot even write an equality function over
this form of type representation. The problem repeats itself in the
definition of |dynApply|, when calling |eqTyCon tarrow TArrow|. The
call to |eqT| in |dynApply|, on the other hand, \emph{could} be homogeneous,
as we would know at that point that the types represented by |targ| and
|targ'| are both of kind |Type|.

In today's Haskell, the lack of heterogeneous equality means that |dynApply|
must rely critically on |unsafeCoerce|. With heterogeneous equality, 
|dynApply| can remain safely outside the trusted code base.

%if style == poly
%include effects.lhs
%endif

\section{Why Haskell?}
\label{sec:why-haskell}

There already exist several dependently typed languages. Why do we need
another? This section presents several reasons why I believe the work
described in this dissertation will have impact.

\subsection{Increased reach}
\label{sec:haskell-in-industry}

Haskell currently has some level of adoption in industry.\footnote{At the
time of writing, \url{https://wiki.haskell.org/Haskell_in_industry}
lists 81 companies who use Haskell to some degree. That page, of course,
is world-editable and is not authoritative. However, I am personally aware
of Haskell's (growing) use in several industrial settings, and I have seen
quite a few job postings looking for Haskell programmers in industry. For
example, see \url{http://functionaljobs.com/jobs/search/?q=haskell}.}
Haskell is also used as the language of choice in several academic
programs used to teach functional programming. There is also the ongoing
success of the Haskell Symposium. These facts all indicate that the
Haskell community is active and sizeable. If GHC, the primary Haskell
compiler, offers dependent types, more users will have immediate
access to dependent types than ever before.

The existing dependently typed languages were all created, more or less, as
playgrounds for dependently typed programming. For a programmer to choose to
write her program in an existing dependently typed language, she would have to
be thinking about dependent types (or the possibility of dependent types) from
the start. However, Haskell is, first and foremost, a general purpose
functional programming language. A programmer might start his work in Haskell
without even being aware of dependent types, and then as his experience grows,
decide to add rich typing to a portion of his program.

With the increased exposure GHC would offer to dependent types, the academic
community will gain more insight into dependent types and their practical
use in programs meant to get work done.

\subsection{Backward-compatible type inference}

Working in the context of Haskell gives me a stringent, immovable constraint:
my work must be backward compatible. In the new version of GHC that supports
dependent types, all current programs must continue to compile. In particular,
this means that type inference must remain able to infer all the types it does
today, including types for definitions with no top-level annotation. Agda and
Idris require a top-level type annotation for every function; Coq uses
inference where possible for top-level definitions but is sometimes
unpredictable. Furthermore, Haskellers expect the type inference engine
to work hard on their behalf; they wish to rarely rely on manual proving
techniques.

The requirement of backward compatibility keeps me honest in my design of
type inference---I cannot cheat by asking the user for more information. The
technical content of this statement is discussed in \pref{cha:type-inference}
by comparison with the work of \citet{outsidein} and \citet{visible-type-application}.
See Sections~\ref{sec:oi} and~\ref{sec:sb}.
A further advantage of
working in Haskell is that the type inference of Haskell is well studied in
the literature. This dissertation continues this tradition in
\pref{cha:type-inference}.

\subsection{No termination or totality checking}
\label{sec:no-termination-check}
\label{sec:no-proofs}

Many dependently typed languages today strive to be proof systems as well
as programming languages. These care deeply about
totality: that all pattern matches consider all possibilities and that
every function can be proved to terminate. Coq does not accept a function
until it is proved to terminate. Agda behaves likewise, although the
termination checker can be disabled on a per-function basis. Idris
embraces partiality, but then refuses to evaluate partial functions during
type-checking. Dependent Haskell, on the other hand, does not care
about totality.

Dependent Haskell emphatically does \emph{not} strive to be a proof system.
In a proof system, whether or not a type is inhabited is equivalent to whether
or not a proposition holds. Yet, in Haskell, \emph{all} types are inhabited,
by |undefined| and other looping terms, at a minimum. Even at the type level,
all kinds are inhabited by the following type family, defined in GHC's
standard library:
\begin{code}
type family Any :: k  -- no instances
\end{code}
The type family |Any| can be used at any kind, and so inhabits all kinds.

Furthermore, Dependent Haskell has the |Type : Type| axiom, meaning that instead of
having an infinite hierarchy of universes characteristic of Coq, Agda, and
Idris, Dependent Haskell has just one universe, which contains itself. It is
well known that self-containment of this form leads to logical inconsistency
by enabling the construction of a looping term~\cite{girard-thesis}, but I am
unbothered by this---Haskell has many other looping terms, too! (See
\pref{sec:type-in-type} for more discussion on this point.)
By allowing ourselves to have |Type : Type|, the type system
is much simpler than in systems with a hierarchy of universes.

There are two clear downsides of the lack of totality:
\begin{itemize}
\item What appears to be a proof might not be. Suppose we need to prove
that type |tau| equals type |sigma| in order to type-check a program.
We can always use $|undefined :: tau :~~: sigma|$ to prove this equality,
and then the program will type-check. The problem will be discovered only
at runtime. Another way to see this problem is that equality proofs must
be run, having an impact on performance. However, note that we cannot
use the bogus equality without evaluating it; there is no soundness issue.

This drawback is indeed serious, and important future work includes
designing and implementing a totality checker for Haskell. (See
the work of \citet{liquid-haskell} for one approach toward this goal.
Recent work by \citet{gadts-meet-their-match} is another key building block.)
Unlike in other languages, though, the totality checker would be chiefly
used in order to optimize away proofs, rather than to keep the language
safe. Once the checker is working, we could also add compiler flags to
give programmers compile-time warnings or errors about partial functions,
if requested.

\item Lack of termination in functions used at the type level might
conceivably cause GHC to loop. This is not a great concern, however,
because the loop is directly caused by a user's type-level program.
In practice, GHC counts steps it uses in reducing types and reports
an error after too many steps are taken. The user can, via a compiler
flag, increase the limit or disable the check.
\end{itemize}

The advantages to the lack of totality checking are that Dependent Haskell
is simpler for not worrying about totality. It is also more expressive,
treating partial functions as first-class citizens.

\subsection{GHC is an industrial-strength compiler}

Hosting dependent types within GHC is likely to reveal new insights about
dependent types due to all of the features that GHC offers. Not only are
there many surface language extensions that must be made to work with
dependent types, but the back end must also be adapted. A dependently typed
intermediate language must, for example, allow for optimizations. Working
in the context of an industrial-strength compiler also forces the implementation
to be more than just ``research quality,'' but ready for a broad audience.

\subsection{Manifest type erasure properties}

A critical property of Haskell is that it can erase types. Despite all the
machinery available in Haskell's type system, all type information can be
dropped during compilation. In Dependent Haskell, this does not change.
However, dependent types certainly blur the line between term and type, and
so what, precisely, gets erased can be difficult to discern. Dependent Haskell,
in a way different from other dependently typed languages, makes clear which
arguments to functions (and data constructors) get erased. This is through
the user's choice of relevant vs.~irrelevant quantifiers, as explored in
\pref{sec:relevance}. Because erasure properties are manifestly available
in types, a performance-conscious user can audit a Dependent Haskell program
and see exactly what will be removed at runtime.

It is possible that, with practice, this ability will become burdensome, in
that the user has to figure out what to keep and what to discard. Idris's
progress toward type erasure analysis~\cite{erasing-indices,practical-erasure} may benefit Dependent Haskell as well.

\subsection{Type-checker plugin support}

Recent versions of GHC allow \emph{type-checker plugins},
a feature that allows end users to write a custom
solver for some domain of interest. For example, \citet{type-checker-plugins}
uses a plugin to solve constraints arising from using Haskell's type system
to check that a physical computation respects units of measure. As
another example, \citet{diatchki-smt-plugin} has written a plugin that
uses an SMT solver to work out certain numerical constraints that can
arise using GHC's type-level numbers feature.

Once Haskell is equipped with dependent types, the need for these plugins will only
increase. However, because GHC already has this accessible interface,
the work of developing the best solvers for Dependent Haskell can be
distributed over the Haskell community. This democratizes the development
of dependently typed programs and spurs innovation in a way a centralized
development process cannot.

\subsection{Haskellers want dependent types}

The design of Haskell has slowly been marching toward having dependent types.
Haskellers have enthusiastically taken advantage of the new features. For
example, over 1,000 packages published at \url{hackage.haskell.org} use type
families~\cite{injective-type-families}. Anecdotally, Haskellers are excited
about getting full dependent types, instead of just faking
them~\cite{faking-it,she,singletons}. Furthermore, with all of the type-level
programming features that exist in Haskell today, it is a reasonable step
to go to full dependency.

%%  LocalWords:  newcode rae fmt endif STLC STLC's Ty infixr featureful Elem
%%  LocalWords:  glambda Bruijn EZ xs ES Expr Var ctx ty Lam arg App TT elt
%%  LocalWords:  Val LamVal TTVal eval de subst poly LZ LS ys len StepResult
%%  LocalWords:  SameValue hasochism zipWith Typeable HRefl TyCon TypeRep eqT
%%  LocalWords:  TyApp eqTyCon tyCon Dyn dynApply TArrow unsafeCoerce Foo cha
%%  LocalWords:  editable DependentTypes MonoLocalBinds outsidein concat Exts
%%  LocalWords:  SingTH TypeLits TL Vec Succ Num abs signum fromInteger fst
%%  LocalWords:  listReplicate proj sig gradyear Morley Aimee Barnett Peng Qi
%%  LocalWords:  Oliveira Chakraborty Sangeeta Kumar Xu NameSchema Col queryDB
%%  LocalWords:  printName putStrLn sch loadTable putStr getLine mapM RA Eq
%%  LocalWords:  elementOf ghci withSchema checkSchema loadSchema checkIn SI
%%  LocalWords:  Buckwalter Listify NumArgs NAZero NASucc listApply args targ
%%  LocalWords:  CountArgs CNumArgs numArgs getNA ScopedTypeVariables tarrow
%%  LocalWords:  tres
