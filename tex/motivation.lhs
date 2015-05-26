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
data Val :: Ty -> * where
  LamVal  :: Expr ![arg] res ->  Val (arg !:~> res)
  TTVal   ::                     Val !Unit
\end{code}

Our big-step evaluator has a straightforward type:
\begin{code}
eval :: Expr ![] ty -> Val ty
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
any testing. In such a delicate operation, this is wonderful, indeed.

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
big-step semantics -- to remain the same. We thus want the small-step stepper
to return a pair: the new expression (or value), and evidence that the value
of the expression (as given by the big-step evaluator) remains the same.

We thus need a |StepResult| datatype:
\begin{noway}
\begin{spec}
data StepResult :: Expr ![] ty -> * where
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
followed by regular arguments. Generalizing this form does not provide any
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
Due to GHC's ability to freely use assumed equality assumptions, |step|
requires no explicit manipulation of equality proofs. Let's look at the |App|
case above. We first check whether or not |e1| can take a step. If it can,
we get the result of the step |e1'|, \emph{and} a proof that |!eval e1 ~ !eval e1'|.
This proof enters into the typechecking context and is invisible in the program
text. On the right-hand side of the match, we conclude that |App e1 e2| steps to
|App e1' e2|. This requires a proof that |!eval (App e1 e2) ~ !eval (App e1' e2)|.
Reducing |!eval| on both sides of that equality gives us
|!eval (!apply (!eval e1) e2) ~ !eval (!apply (!eval e1') e2)|. Since we know
|!eval e1 ~ !eval e1'|, however, this equality is easily solvable; GHC does the
heavy lifting for us. Similar reasoning proves the equality in the second branch
of the |case|, and the other clauses of |step| are straightforward.

The ease in which these equalities are solved is unique to Haskell. I have
translated this example to Coq, Agda, and Idris; each has its shortcomings:
\begin{itemize}
\item Coq deals quite poorly with indexed types, such as |Expr|. The problem appears
to stem from Coq's weak support for dependent pattern matching. For example, if we
inspect a |ctx| to discover that it is empty, Coq, by default, forgets the
equality |ctx = []|. It then, naturally, fails to use the equality to rewrite
the types of the right-hand sides of the pattern match. This can be overcome through
various tricks, but it is far from easy.

\item Agda does a better job with indexed types, but it is not designed around
implicit proof search. A key part of Haskell's elegance in this example is that
pattern-matching on a |StepResult| reveals an equality proof to the type-checker,
and this proof is then used to rewrite types in the body of the pattern match. This
all happens without any direction from the programmer. In Agda, on the other hand,
the equality proofs must be unpacked and used with Agda's \keyword{rewrite} tactic.

\item Idris also runs aground with this example. The |eval| function is indeed a total
function -- it does not fail for any arguments, and it is guaranteed to terminate.
However, proving that |eval| terminates is not easy: it amounts to proving that
the simply-typed lambda calculus has normal forms (and that |eval| finds those
normal forms). Without such a proof encoded in the program, Idris treats |eval| as
a partial function and refuses to reduce it in types.
\end{itemize}

\begin{proposal}
The above limitations in Coq, Agda, and Idris are from my experimentation. I am
not an expert in any of these languages, and I will consult experts before the
final dissertation.
\end{proposal}

\subsubsection{Conclusion}

We have built up a small-step stepper whose behavior is verified against a
big-step evaluator. Despite this extra checking, the |step| function will run
in an identical manner to one that is unchecked -- there is no runtime effect
of the extra verification. We can be sure of this because we can audit the
types involved and see that only the expression itself is around at runtime;
the rest of the arguments (the indices and the equality proofs) are erased.
Furthermore, getting this all done is easier and more straightforward in
Dependent Haskell than in the other three dependently typed languages I
tried.

%% To pull this off, we will need a dependent pair, or $\Sigma$-type:
%% %format :&: = "\mathop{{:}{\&}{:}}"
%% \begin{notyet}
%% \begin{spec}
%% data Sigma (s :: *) (t :: s -> *) where
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
