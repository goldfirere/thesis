%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt
%endif


\chapter{Motivation}
\label{cha:motivation}

Functional programmers use dependent types in two primary ways, broadly
speaking: in order to eliminate erroneous programs from being accepted, and in
order to write intricate programs that a simply-typed language cannot accept.
In this chapter, we will motivate the use of dependent types from both of
these angles. The chapter concludes with a section motivating why Haskell, in
particular, is ripe for dependent types.

As a check for accuracy in these examples, all the indented, typeset code
throughout this dissertation is type-checked against my implementation
every time the text is typeset.

\begin{proposal}
In this proposal, I elide the details of the motivating examples. Instead,
I list them as stubs to be filled out later, when writing the dissertation
proper.

The code snippets throughout this dissertation are presented on a variety
of background colors. A \colorbox{working}{\workingcolorname} background
highlights code that does not work in today's Haskell but does currently
(May 2015) work in my implementation. A \colorbox{notyet}{\notyetcolorname}
background indicates code that does not work in my implementation, but could
still be implemented via the use of singletons~\cite{singletons}
and similar workarounds. A \colorbox{noway}{\nowaycolorname}
background marks code that does not currently work in my implementation
due to bugs and incompleteness in my implementation. To my knowledge,
there is nothing more than engineering (and perhaps the use of singletons)
to get these examples working.
\end{proposal}

\section{Eliminating erroneous programs}

\subsection{Simple example: Length-indexed vectors}

\subsection{A strongly typed simply typed lambda calculus interpreter}
\label{sec:stlc}

It is straightforward to write an interpreter for the simply typed lambda
calculus (STLC) in Haskell. However, how can we be sure that our interpreter
is written correctly? Using some features of dependent types -- notably,
generalized algebraic datatypes, or GADTs -- we can incorporate the STLC's
type discipline into our interpreter. Using the extra features in Dependent
Haskell, we can then write both a big-step semantics and a small-step
semantics and have GHC check that they correspond.

\subsubsection{Type definitions}

Our first step is to write a type to represent the types in our lambda-calculus:
\begin{code}
data Ty = Unit | Ty :~> Ty
infixr 0 :~>
\end{code}
I choose |Unit| as our one and only base type, for simplicity. This calculus
is clearly not suitable for computation, but it demonstrates the use of GADTs
well. The model described here scales up to a more featureful
lambda-calculus.\footnote{For example, see my work on \package{glambda} at
  \url{https://github.com/goldfirere/glambda}.}
The |infixr| declaration declares that the constructor |:~>| is right-associative,
as usual.

We are then confronted quickly with the decision of how to encode bound
variables. Let's choose de Bruijn indices~\cite{debruijn}, as these are well-known
and conceptually simple. However, instead of using natural numbers to
represent our variables, we'll use a custom |Elem| type:
\begin{code}
data Elem :: [a] -> a -> * ^^ where
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
data Expr :: [Ty] -> Ty -> * ^^ where
  Var  :: Elem ctx ty                              ->  Expr ctx ty
  Lam  :: Expr (arg !: ctx) res                    ->  Expr ctx (arg !:~> res)
  App  :: Expr ctx (arg !:~> res) -> Expr ctx arg  ->  Expr ctx res
  TT   ::                                              Expr ctx !Unit
\end{code}
Like with |Elem list elt|, a value of type |Expr ctx ty| serves two purposes:
it records the structure of our expression, \emph{and} it proves a property,
namely that the expression is well-typed in context |ctx| with type |ty|.
Indeed, with some practice, we can read off the typing rules for the simply
typed lambda calculus direct from |Expr|'s definition. In this way, it is
impossible to create an ill-typed |Expr| (ignoring the possibility of
|undefined|).

\subsubsection{Big-step evaluator}

We now wish to write both small-step and big-step operational semantics
for our expressions. First, we'll need a way to denote values in our language:
\begin{code}
data Val :: [Ty] -> Ty -> * where
  LamVal  :: Expr (arg !: ctx) res ->  Val ctx (arg !:~> res)
  TTVal   ::                           Val ctx !Unit
\end{code}

Our big-step evaluator has a straightforward type:
\begin{code}
eval :: Expr ![] ty -> Val ![] ty
\end{code}
This type says that a well-typed, closed expression (that is, the context
is empty) can evaluate to a well-typed, closed value, of the same type |ty|.
Only a type-preserving evaluator will have that type, so GHC can check
the type-soundness of our lambda calculus as it compiles our interpreter.

Of course, to implement |eval|, we'll need several auxiliary functions, each
with intriguing types:
\begin{code}
-- Shift the de Bruijn indices in an expression
shift :: forall ctx ty x. Expr ctx ty -> Expr (x !: ctx) ty

-- Substitute one expression into another
subst :: forall ctx s ty. Expr ctx s -> Expr (s !: ctx) ty -> Expr ctx ty

-- Perform $\beta$-reduction
apply :: Val ctx (arg !:~> res) -> Expr ctx arg -> Expr ctx res
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
induction hypothesis'' for |shift| and |subst|; in this context, I mean
that we need an internal recursive function with extra arguments.
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
    go :: forall ty. pi ctx0 -> Expr (ctx0 !++ s !: ctx) ty -> Exp (ctx0 !++ ctx) ty
    go = ...
\end{spec}
\end{notyet}
%
%if style == newcode
\begin{code}
data Length :: [a] -> * where
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
convention of using |!| to promote constructors from terms to types.)
The |go| functions also $\Pi$-quantify over |ctx0|, meaning that the value
of this context prefix is available in types (as we can see) and also at
runtime. This is necessary because the functions need the length of |ctx0|
at runtime, in order to know how to shift or substitute. Note also the
syntax |pi ctx0 ->|, where the $\Pi$-bound variable is followed by an |->|.
The use of an arrow here (as opposed to a |.|) indicates that the parameter
is \emph{visible} in source programs; the empty list is passed in visibly
in the invocation of |go|. The final interesting
feature of these types is that they re-quantify |ty|. This is necessary because
the recursive invocations of the functions may be at a different type than the
outer invocation. The other type variables in the types are lexically bound
by the |forall| in the type signature of the outer function.

The implementation of these functions is fiddly and uninteresting, and is
omitted from this text. However, writing this implementation is made much
easier by the precise types. If I were to make a mistake in the delicate
de Bruijn shifting operation, I would learn of my mistake immediately, without
any testing. In such a fiddly operation, this is wonderful, indeed.

With all of these supporting functions written, the evaluator itself is
dead simple:
\begin{code}
eval (Var v)      = case v of {}  -- no variables in an empty context
eval (Lam body)   = LamVal body
eval (App e1 e2)  = eval (apply (eval e1) e2)
eval TT           = TTVal
\end{code}

\subsubsection{Small-step stepper}
We now turn to writing the small-step semantics. We could proceed in
a very similar fashion to the big-step semantics, by defining a |step|
function that steps an expression either to another expression or to
a value. But we want better than this.

Instead, we want to ensure that the small-step semantics respects the big-step
semantics. That is, after every step, we want the value -- as given by the
big-step semantics -- to remain the same.

\subsection{Units-of-measure}

\subsection{Machine-checked sorting algorithm}

\subsection{Type-safe database access}

See also other examples in \citet{power-of-pi} and \citet{hasochism}.

\section{Encoding hard-to-type programs}

\subsection{Variable-arity |zipWith|}

\subsection{Deconstructing runtime types}

\subsection{Inferred algebraic effects}

\cite{algebraic-effects}

\section{Why Haskell?}

\begin{proposal}
This section will be an expansion of the issues raised in the introduction, citing
community interest in dependent types, and the plethora of attempts to encode
dependent types in today's Haskell.

A further part of this section will counter a common argument along the lines of
``If we want Haskell with dependent types, why not just use Agda or Idris?'' There
will be several main points:

\begin{itemize}
\item Haskell is a richer language than Idris or Agda. Studying the interaction
between dependent types and Haskell's other features is illuminating.

\item Implementing dependent types in Haskell requires backward compatibility.
Since my work is intended to be merged with the main releases of GHC, all current
programs must continue to be accepted and retain their meanings. This requirement
puts interesting constraints on type inference, and it will not allow me to take
any shortcuts around pre-existing code.

\item Haskell has more users than Agda or Idris, and having dependent types
available in Haskell will further our knowledge about dependent types, as more
people can experiment with them.
\end{itemize}
\end{proposal}

\subsection{No termination checking}
\label{sec:termination}
