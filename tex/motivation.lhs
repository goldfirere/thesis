%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}
import Data.Kind ( type (*) )
\end{code}

%endif


\chapter{Motivation}
\label{cha:motivation}

Functional programmers use dependent types in two primary ways, broadly
speaking: in order to eliminate erroneous programs from being accepted, and in
order to write intricate programs that a simply-typed language cannot accept.
In this chapter, we will motivate the use of dependent types from both of
these angles. The chapter concludes with a section motivating why Haskell, in
particular, is ripe for dependent types.

As a check for accuracy in these examples and examples throughout this
dissertation, all the indented, typeset code
is type-checked against my implementation
every time the text is typeset.

\rae{Revisit.}
The code snippets throughout this dissertation are presented on a variety of
background colors. A \colorbox{working}{\workingcolorname} background
highlights code that newly works in GHC~8.0 due to my implementations
of previously published papers~\cite{nokinds,visible-type-application}.
A \colorbox{notyet}{\notyetcolorname}
background indicates code that does not work verbatim,
but could still be implemented via the use of singletons~\cite{singletons} and
similar workarounds. A \colorbox{noway}{\nowaycolorname} background marks code
that does not currently work in my implementation due to bugs and
incompleteness in my implementation. To my knowledge, there is nothing more
than engineering (and perhaps the use of singletons) to get these examples
working.

\section{Eliminating erroneous programs}

\subsection{Simple example: Length-indexed vectors}
\label{sec:length-indexed-vectors}
\rae{Make sure |replicate| is here. It's referenced later.}
\rae{There will be overlap between this section and \pref{sec:pattern-matching}.
Double-check it.}

\subsection{A strongly typed simply typed lambda calculus interpreter}
\label{sec:stlc}

It is straightforward to write an interpreter for the simply typed lambda
calculus (STLC) in Haskell. However, how can we be sure that our interpreter
is written correctly? Using some features of dependent types---notably,
generalized algebraic datatypes, or GADTs---we can incorporate the STLC's
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
data Val :: Ty -> * ^^ where
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
    go :: forall ty. pi ctx0 -> Expr (ctx0 !++ s !: ctx) ty -> Expr (ctx0 !++ ctx) ty
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
in the invocation of |go|. (See also \pref{sec:visibility}.) The final interesting
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
semantics. That is, after every step, we want the value---as given by the
big-step semantics---to remain the same. We thus want the small-step stepper
to return a custom datatype, marrying the result of stepping with evidence
that the value of this result agrees with the value of the original expression:\footnote{This example fails because it contains data constructors with constraints
occurring after visible parameters, something currently unsupported by GHC.
If the $\Pi$-bound parameters were invisible, this would work.}
\begin{noway}
\begin{spec}
data StepResult :: Expr ![] ty -> * ^^ where
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
This proof enters into the type-checking context and is invisible in the program
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
various tricks, but it is far from easy. Furthermore, even once these challenges
are surmounted, it is necessary to prove that |eval| terminates---a non-trivial
task---for Coq to
accept the function.

\item Agda does a better job with indexed types, but it is not designed around
implicit proof search. A key part of Haskell's elegance in this example is that
pattern-matching on a |StepResult| reveals an equality proof to the type-checker,
and this proof is then used to rewrite types in the body of the pattern match. This
all happens without any direction from the programmer. In Agda, on the other hand,
the equality proofs must be unpacked and used with Agda's \keyword{rewrite} tactic.
In Agda, disabling the termination checker for |eval| is easy: simply use the
@{-# NO_TERMINATION_CHECK #-}@ directive.

%{
%format assert_total = "\keyword{assert\_total}"
\item Idris also runs into some trouble with this example. Like Agda, Idris
works well with indexed types. The |eval| function is unsurprisingly inferred
to be partial, but this is easy enough to fix with a well-placed
|assert_total|. However, Idris's proof search mechanism appears to be unable
to find proofs that |step| is correct in the |App| cases. (Using an \keyword{auto}
variable, Idris is able to find the proofs automatically in the other |step|
clauses.) Idris comes the closest to Haskell's brevity in this example, but
it still requires two explicit, if short, places where equality proofs must
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
about termination (more discussion in \pref{sec:no-termination-check}) and
has an aggressive rewriting engine used to solve equality predicates.

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

See also other examples in the work of \citet{power-of-pi} and \citet{hasochism}.

\section{Encoding hard-to-type programs}

\subsection{Variable-arity |zipWith|}

\begin{proposal}
This will be adapted from previous work~\cite{closed-type-families-extended}.
\end{proposal}

\subsection{Typed reflection}

\emph{Reflection} is the act of reasoning about a programming language from
within programs written in that language.\footnote{Many passages in this
  example come verbatim from a draft paper of mine~\cite{overabundance-of-equalities}.} In
Haskell, we are naturally concerned with reflecting Haskell types. A
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

Here is our desired representation:
%
\begin{code}
data TyCon (a :: k)
  -- abstract; |Int| is represented by a |TyCon Int|
data TypeRep (a :: k) where
  TyCon  :: TyCon a -> TypeRep a
  TyApp  :: TypeRep a -> TypeRep b -> TypeRep (a b)
\end{code}
%
For every new type declared, the compiler would supply an appropriate value of
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
kind |*|, and |Maybe| is at kind |* -> *|. Thus, when comparing two
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
a |Bool|. When the types indeed equal, we get evidence that GHC can use to
be away of this type equality during type-checking. A simple return type of
|Bool| would not give the type-checker any information.

\subsubsection{Dynamic typing}

Now that we have a type representation with computable equality, we
can package that representation with a chunk of data, and so form a
dynamically typed package:
%
\begin{code}
data Dyn where
  Dyn :: forall (a :: *). TypeRep a -> a -> Dyn
\end{code}

The |a| type variable there is an \emph{existential} type variable. We can
think of this type as being part of the data payload of the |Dyn| constructor;
it is chosen at construction time and unpacked at pattern-match time.
Because of the |TypeRep a| argument, we can learn more about |a| after
unpacking. (Without the |TypeRep a| or some other type-level information
about |a|, the unpacking code must treat |a| as an
unknown type and must be parametric in the choice of type for |a|.)

Using |Dyn|, we can pack up arbitrary
data along with its type, and push that data across a network. The receiving
program can then make use of the data, without needing to subvert Haskell's
type system. The type representation library must be trusted to recreate
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

\subsubsection{Discussion}

Heterogeneous equality is necessary throughout this example. It first is
necessary in the definition of |eqT|. In the |TyApp| case, we compare |a1|
to |a2|. If we had only homogeneous equality, it would be necessary that
the types represented by |a1| and |a2| be of the same kind. Yet, we can't
know this here! Even if the types represented by |TyApp a1 b1| and
|TyApp a2 b2| have the same kind, it is possible that |a1| and |a2| would
not. (For example, maybe the type represented by |a1| has kind |* -> *|
and the type represented by |a2| has kind |Bool -> *|.) With only
homogeneous equality, we cannot even write an equality function over
this form of type representation. The problem repeats itself in the
definition of |dynApply|, when calling |eqTyCon tarrow TArrow|. The
call to |eqT| in |dynApply|, on the other hand, \emph{could} be homogeneous,
as we would know at that point that the types represented by |targ| and
|targ'| are both of kind |*|.

In today's Haskell, the lack of heterogeneous equality means that |dynApply|
must rely critically on |unsafeCoerce|. With heterogeneous equality, we can
see that |dynApply| can remain safely outside the trusted code base.

\subsection{Inferred algebraic effects}

\begin{proposal}
This section will contain a Haskell translation of Idris's implementation of
algebraic effects~\cite{algebraic-effects}. The algebraic effects library
allows Idris code to compose effects in a more modular way than can be done
with Haskell's monad transformers. It relies critically on dependent types.
\end{proposal}

\section{Why Haskell?}
\label{sec:why-haskell}

There already exist several dependently typed languages. Why do we need
another? This section presents several reasons why I believe the work
described in this dissertation will have impact.

\subsection{Increased reach}

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
to work hard on their behalf and should rarely resort to manual proving
techniques.

The requirement of backward compatibility ``keeps me honest'' in my design of
type inference---I cannot cheat by asking the user for more information. The
technical content of this statement is discussed in \pref{cha:type-inference}
by comparison with the work of \citet{outsidein} and \citet{visible-type-application}.
See Sections~\ref{sec:oi} and~\ref{sec:sb}.
A further advantage of
working in Haskell is that the type inference of Haskell is well-studied in
the literature. This dissertation continues this tradition in
\pref{cha:type-inference}.

\subsection{No termination or totality checking}
\label{sec:no-termination-check}
\label{sec:no-proofs}

Existing dependently typed languages strive to be proof systems as well
as programming languages. (A notable exception is Cayenne~\cite{cayenne},
which also omits termination checking,
but that language seems to have faded into history.) They care deeply about
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

Furthermore, Dependent Haskell has the |* :: *| axiom, meaning that instead of
having an infinite hierarchy of universes characteristic of Coq, Agda, and
Idris, Dependent Haskell has just one universe which contains itself. It is
well-known that self-containment of this form leads to logical inconsistency
by enabling the construction of a looping term~\cite{girard-thesis}, but we are
unbothered by this. By allowing ourselves to have |* :: *|, the type system
is much simpler than in systems with a hierarchy of universes.

There are two clear downsides of the lack of totality:
\begin{itemize}
\item What appears to be a proof might not be. Suppose we need to prove
that type |tau| equals type |sigma| in order to type-check a program.
We can always use $|undefined :: tau :~~: sigma|$ to prove this equality,
and then the program will type-check. The problem will be discovered only
at runtime. Another way to see this problem is that equality proofs must
be run, having an impact on performance.

This drawback is indeed serious, and important future work includes
designing and implementing a totality checker for Haskell. (See
the work of \citet{liquid-haskell} for one approach toward this goal.
Recent work by \citet{gadts-meet-their-match} is another key building block.)
Unlike in other languages, though, the totality checker would be chiefly
used in order to optimize away proofs, rather than to keep the language
safe. Once the checker were working, we could also add compiler flags to
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
is simpler for not worrying about totality, and also that by using
Dependent Haskell, we will learn more about dependent types in the presence
of partiality.

\subsection{GHC is an industrial-strength compiler}

Hosting dependent types within GHC is likely to reveal new insights about
dependent types due to all of the features that GHC offers. Not only are
there many surface language extensions that must be made to work with
dependent types, but the back end must also be adapted. A dependently typed
intermediate language must, for example, allow for optimizations. Working
in the context of an industrial-strength compiler also forces the implementation
to be more than just ``research quality'', but ready for a broad audience.

\subsection{Manifest type erasure properties}

A critical property of Haskell is that it can erase types. Despite all the
machinery available in Haskell's type system, all type information can be
dropped during compilation. In Dependent Haskell, this does not change.
However, dependent types certainly blur the line between term and type, and
so what, precisely, gets erased can be less clear. Dependent Haskell,
in a way different from other dependently typed languages, makes clear which
arguments to functions (and data constructors) get erased. This is through
the user's choice of relevant vs.~irrelevant quantifiers, as explored in
\pref{sec:relevance}. Because erasure properties are manifestly available
in types, a performance-conscious user can audit a Dependent Haskell program
and see exactly what will be removed at runtime, aiming to meet any particular
performance goals the user has.

It is possible that, with practice, this ability will become burdensome, in
that the user has to figure out what to keep and what to discard. Idris's
progress toward type erasure analysis~\cite{erasing-indices,practical-erasure} may benefit Dependent Haskell as well.

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
%%  LocalWords:  editable DependentTypes MonoLocalBinds outsidein
