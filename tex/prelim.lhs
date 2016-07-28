%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}
import Data.Set ( Set )
import qualified Data.Set as Set
import Data.Primitive.ByteArray ( ByteArray )
import Data.Vector ( Vector )
import Prelude hiding ( Maybe(..), Bool(..) )
import GHC.Exts ( Constraint, fromString )
import Data.List ( intercalate )
import Data.Kind ( type (*) )
\end{code}

%endif

\chapter{Preliminaries}
\label{cha:prelim}

This chapter is a primer of type-level programming facilities that exist
in today's Haskell. It serves both as a way for readers less experienced
in Haskell to understand the remainder of the dissertation, and as a point
of comparison against the Dependent Haskell language I describe in
\pref{cha:dep-haskell}. Those more experienced with Haskell may easily
skip this chapter. However, all readers may wish to consult \pref{app:typo}
to learn the typographical conventions used throughout this dissertation.

I assume that the reader is comfortable with a typed functional programming
language, such as Haskell98 or a variant of ML.

\section{Type classes and dictionaries}
\label{sec:type-classes}

Haskell supports type classes~\cite{type-classes}. An example is worth
a thousand words:
%{
%if style == poly
%format MyShow = Show
%format myShow = show
%endif
\begin{code}
class MyShow a where
  myShow :: a -> String
instance MyShow Bool where
  myShow True   = "True"
  myShow False  = "False"
\end{code}
This declares the class |MyShow|, parameterized over a type variable |a|,
with one method |myShow|. The class is then instantiated at the type |Bool|,
with a custom implementation of |myShow| for |Bool|s. Note that, in the
|MyShow Bool| instance, the |myShow| function can use the fact that
|a| is now |Bool|: the one argument to |myShow| can be pattern-matched
against |True| and |False|. This is in stark contrast to the usual
parametric polymorphism of a function |show' :: a -> String|, where the
body of |show'| \emph{cannot} assume any particular instantiation for |a|.

With |MyShow| declared, we can now use this as a constraint on types. For
example:
\begin{code}
smooshList :: MyShow a => [a] -> String
smooshList xs = concat (map myShow xs)
\end{code}
The type of |smooshList| says that it can be called at any type |a|, as
long as there exists an instance |MyShow a|. The body of |smooshList|
can then make use of the |MyShow a| constraint by calling the |myShow|
method. If we leave out the |MyShow a| constraint, then the call to |myShow|
does not type-check. This is a direct result of the fact that the full
type of |myShow| is really |MyShow a => a -> String|. (The |MyShow a| constraint
on |myShow| is implicit, as the method is declared within the |MyShow| class
declaration.) Thus, we need to know that the instance |MyShow a| exists
before calling |myShow| at type |a|.

Operationally, type classes work by passing
\emph{dictionaries}~\cite{type-classes-impl}. A type class dictionary is
simply a record containing all of the methods defined in the type class.
It is as if we had these definitions:
\begin{code}
data ShowDict a = MkShowDict { showMethod :: a -> String }

showBool :: Bool -> String
showBool True   = "True"
showBool False  = "False"

showDictBool :: ShowDict Bool
showDictBool = MkShowDict showBool
\end{code}
Then, whenever a constraint |MyShow Bool| must be satisfied, GHC produces
the |showDictBool| dictionary. This dictionary actually becomes a runtime
argument to functions with a |MyShow| constraint. Thus, in a running program,
the |smooshList| function actually takes 2 arguments: the dictionary
corresponding to |MyShow a| and the list |[a]|.
%}

\section{Families}

\subsection{Type families}
A \emph{type family}~\cite{chak1, chak2, closed-type-families}
is simply a function on types. (I sometimes use ``type function''
and ``type family'' interchangeably.) Here is an uninteresting example:
%if style == poly
%format F1
%format F2
%format useF1
%endif
\begin{code}
type family F1 a where
  F1 Int   = Bool
  F1 Char  = Double

useF1 :: F1 Int -> F1 Char
useF1 True   = 1.0
useF1 False  = (-1.0)
\end{code}
We see that GHC simplifies |F1 Int| to |Bool| and |F1 Char| to |Double|
in order to typecheck |useF1|.

|F1| is a \emph{closed} type family, in that all of its defining equations
are given in one place. This most closely corresponds to what functional
programmers expect from their functions. Today's Haskell also supports
\emph{open} type families, where the set of defining equations can be
extended arbitrarily. Open type families interact particularly well
with Haskell's type classes, which can also be
extended arbitrarily. Here is a more interesting example than the one above:
%
\begin{code}
type family Element c
class Collection c where
  singleton :: Element c -> c

type instance Element [a] = a
instance Collection [a] where
  singleton x = [x]

type instance Element (Set a) = a
instance Collection (Set a) where
  singleton = Set.singleton
\end{code}
%
Because the type family |Element| is open, it can be extended whenever a
programmer creates a new collection type.

Often, open type families are extended in close correspondence with a type
class, as we see here. For this reason, GHC supports \emph{associated}
open type families, using this syntax:
\begin{code}
class Collection' c where
  type Element' c
  singleton' :: Element' c -> c

instance Collection' [a] where
  type Element' [a] = a
  singleton' x = [x]

instance Collection' (Set a) where
  type Element' (Set a) = a
  singleton' = Set.singleton
\end{code}
Associated type families are essentially syntactic sugar for regular
open type families.

\paragraph{Partiality in type families}
A type family may be \emph{partial}, in that it is not defined over
all possible inputs. This poses no direct problems in the theory or
practice of type families. If a type family is used at a type for
which it is not defined, the type family application is considered
to be \emph{stuck}. For example:
\begin{code}
type family F2 a
type instance F2 Int = Bool
\end{code}
Suppose there are no further instances of |F2|. Then, the type |F2 Char|
is stuck. It does not evaluate, and is equal only to itself.

Because type family applications cannot be used on the left-hand side
of type family equations, it is impossible for a Haskell program to
detect whether or not a type is stuck. This is correct behavior, because
a stuck open type family might become unstuck with the inclusion of more
modules, defining more type family instances.

\subsection{Data families}

A \emph{data family} defines a family of datatypes. An example shows
best how this works:
\begin{code}
data family Array a   -- compact storage of elements of type |a|
data instance Array Bool  = MkArrayBool  ByteArray
data instance Array Int   = MkArrayInt   (Vector Int)
\end{code}
With such a definition, we can have a different runtime representation
for an |Array Bool| as we do for an |Array Int|, something not possible
with more traditional parameterized types.

Data families do not play a large role in this dissertation.

\section{Rich kinds}

\subsection{Kinds in Haskell98}

With type families, we can write type-level programs. But are our type-level
programs correct? We can gain confidence in the correctness of the type-level
programs by ensuring that they are well-kinded. Indeed, GHC does this already.
For example, if we try to say |Element Maybe|, we get a type error saying
that the argument to |Element| should have kind |*|, but |Maybe| has kind
|* -> *|.

Kinds in Haskell are not a new invention; they are mentioned in the Haskell98
report~\cite{haskell98}. Because type constructors in Haskell may appear without
their arguments, Haskell needs a kinding system to keep all the types in line.
For example, consider the library definition of |Maybe|:
\begin{code}
data Maybe a = Nothing | Just a
\end{code}
The word |Maybe|, all by itself, does not really represent a type. |Maybe Int|
and |Maybe Bool| are types, but |Maybe| is not. The type-level constant
|Maybe| needs to be given a type to become a type. The kind-level constant
|*| contains proper types, like |Int| and |Bool|. Thus, |Maybe| has kind
|* -> *|.

Accordingly, Haskell's kind system accepts |Maybe Int| and |Element [Bool]|, but
rejects |Maybe Maybe| and |Bool Int| as ill-kinded.

\subsection{Promoted datatypes}

The kind system in Haskell98 is rather limited. It is generated by the
grammar $\kappa \bnfeq |*| \bnfor \kappa |->| \kappa$, and that's it.
When we start writing interesting type-level programs, this almost-unityped
limitation bites.

Accordingly, \citet{promotion} introduce promoted datatypes. The central
idea behind promoted datatypes is that when we say
\begin{code}
data Bool = False | True
\end{code}
we declare two entities: a type |Bool| inhabited by terms |False| and |True|;
and a kind |Bool| inhabited by types |!False| and |!True|.\footnote{The new
  kind does not get a tick |!| but the new types do. This is to disambiguate a
  promoted data constructor |!X| from a declared type |X|; Haskell maintains
  separate type and term namespaces. The ticks are optional if there is no
  ambiguity, but I will always use them throughout this dissertation.} We can
then use the promoted datatypes for more richly-kinded type-level programming.

A nice, simple example is type-level addition over promoted unary natural
numbers:
\begin{code}
data Nat = Zero | Succ Nat
type family a + b where
  !Zero    + b = b
  !Succ a  + b = !Succ (a + b)
\end{code}
Now, we can say |!Succ !Zero + !Succ (!Succ !Zero)| and GHC will simplify the
type to |!Succ (!Succ (!Succ !Zero))|. We can also see here that GHC does
kind inference on the definition for the type-level |+|. We could also specify
the kinds ourselves like this:
\begin{spec}
data family (a :: Nat) + (b :: Nat) :: Nat where ...
\end{spec}

\citet{promotion} detail certain restrictions in what datatypes can be promoted.
A chief contribution of this dissertation is lifting these restrictions.

\subsection{Kind polymorphism}

A separate contribution of the work of \citet{promotion} is to enable
\emph{kind polymorphism}. Kind polymorphism is nothing more than allowing kind
variables to be held abstract, just like functional programmers frequently
do with type variables. For example, here is a type function that calculates
the length of a type-level list at any kind:
\begin{code}
type family Length (list :: [k]) :: Nat where
  Length ![]        = !Zero
  Length (x !: xs)  = !Succ (Length xs)
\end{code}

Kind polymorphism extends naturally to constructs other than type functions.
Consider this datatype:
\begin{code}
data T f a = MkT (f a)
\end{code}
With the \ext{PolyKinds} extension enabled, GHC will infer a most-general kind
|forall k. (k -> *) -> k -> *| for |T|. In Haskell98, on the other hand, this
type would have kind |(* -> *) -> * -> *|, which is strictly less general.

A kind-polymorphic type has extra, invisible parameters that correspond to
kind arguments. When I say \emph{invisible} here, I mean that the arguments
do not appear in Haskell source code. With the \flag{-fprint-explicit-kinds}
flag, GHC will print kind parameters when they occur. Thus, if a Haskell
program contains the type |T Maybe Bool| and GHC needs to print this type
with \flag{-fprint-explicit-kinds}, it will print |T * Maybe Bool|, making
the |*| kind parameter visible. Today's Haskell makes an inflexible choice
that kind arguments are always invisible, which is relaxed in Dependent
Haskell. See \pref{sec:visibility} for more information on visibility in
Dependent Haskell.

\subsection{Constraint kinds}

\citet{promotion} introduces one final extension to Haskell: constraint kinds.
Haskell allows constraints to be given on types. For example, the type
|Show a => a -> String| classifies a function that takes one argument, of type
|a|. The |Show a =>| constraint means that |a| is required to be a member
of the |Show| type class. Constraint kinds make constraints fully first-class.
We can now write the kind of |Show| as |* -> Constraint|. That is, |Show Int| (for
example) is of kind |Constraint|. |Constraint| is a first-class kind, and can
be quantified over. A useful construct over |Constraint|s is the |Some| type:
\begin{code}
data Some :: (* -> Constraint) -> * ^^ where
  Some :: c a => a -> Some c
\end{code}
If we have a value of |Some Show|, stored inside it must be a term of some
(existentially quantified) type |a| such that |Show a|. When we pattern-match
against the constructor |Some|, we can use this |Show a| constraint. Accordingly,
the following function type-checks (where |show :: Show a => a -> String| is a
standard library function):
\begin{code}
showSomething :: Some Show -> String
showSomething (Some thing) = show thing
\end{code}
Note that there is no |Show a| constraint in the function signature---we get
the constraint from pattern-matching on |Some|, instead.

The type |Some| is useful if, say, we want a heterogeneous list such that every
element of the list satisfies some constraint. That is, |[Some Show]| can have elements
of any type |a|, as long as |Show a| holds:
\begin{code}
heteroList :: [Some Show]
heteroList = [Some True, Some (5 :: Int), Some (Just ())]

printList :: [Some Show] -> String
printList things = "[" ++ intercalate ", " (map showSomething things) ++ "]"
\end{code}
%
\begin{spec}
ghci> putStrLn $ printList heteroList
[True, 5, Just ()]
\end{spec}
%
%if style == newcode
\begin{code}
deriving instance Show a => Show (Maybe a)
deriving instance Show Bool
-- need these for the types defined in this file
\end{code}
%endif

\section{Generalized algebraic datatypes}
\label{sec:prop-equality}

Generalized algebraic datatypes (or GADTs) are a powerful feature that allows
term-level pattern matches to refine information about types. They undergird much
of the programming we will see in the examples in \pref{cha:motivation}, and so
I defer most of the discussion of GADTs to that chapter.

Here, I introduce one particularly important GADT: propositional equality.
The following definition appears now as part of the standard library shipped
with GHC, in the |Data.Type.Equality| module:
%
\begin{code}
data (a :: k) ^^ :~: ^^ (b :: k) where
  Refl :: a :~: a
\end{code}
%
The idea here is that a value of type |tau :~: sigma| (for some |tau| and
|sigma|) represents evidence that the type |tau| is in fact equal to the
type |sigma|. Here is a (trivial) use of this type, also from |Data.Type.Equality|:
%
\begin{code}
castWith :: (a :~: b) -> a -> b
castWith Refl x = x
\end{code}
%
Here, the |castWith| function takes a term of type |a :~: b|---evidence
that |a| equals |b|---and a term of type |a|. It can immediately return
this term, |x|, because GHC knows that |a| and |b| are the same type. Thus,
|x| also has type |b| and the function is well typed.

Note that |castWith| must pattern-match against |Refl|. The reason this is
necessary becomes more apparent if we look at an alternate, entirely
equivalent way of defining
|(:~:)|:
%{
%if style == newcode
%format :~: = ":~::"
%format Refl = "Refll"
%endif
\begin{code}
data (a :: k) ^^ :~: ^^ (b :: k) =
  (a ~ b) => Refl
\end{code}
%}
In this variant, I define the type using the Haskell98-style syntax for
datatypes. This says that the |Refl| constructor takes no arguments, but
does require the constraint that |a ~ b|. The constraint |(~)| is GHC's
notation for a proper type equality constraint. Accordingly, to use
|Refl| at a type |tau :~: sigma|, GHC must know that |tau ~ sigma|---in
other words, that |tau| and |sigma| are the same type. When |Refl| is matched
against, this constraint |tau ~ sigma| becomes available for use in the
body of the pattern match.

Returning to |castWith|, pattern-matching against |Refl| brings |a ~ b| into
the context, and GHC can apply this equality in the right-hand side of the
equation to say that |x| has type |b|.

Operationally, the pattern-match against |Refl| is also important. This
match is what forces the equality evidence to be reduced to a value. As
Haskell is a lazy language, it is possible to pass around equality evidence
that is |undefined|. Matching evaluates the argument, making sure that the
evidence is real. The fact that type equality evidence must exist and be
executed at runtime is somewhat unfortunate. See \pref{sec:no-termination-check}
for some discussion.

\section{Higher-rank types}
\label{sec:higher-rank-types}
Standard ML and Haskell98 both use, essentially, the Hindley-Milner (HM) type
system~\cite{hindley,milner,damas-thesis}. The HM type system allows only \emph{prenex
  quantification}, where a type can quantify over type variables only at the
very top. The system is based on \emph{types}, which have no quantification,
and \emph{type schemes}, which do:
\[
\begin{array}{r@@{\,}c@@{\,}ll}
\tau & \bnfeq & \alpha \bnfor H \bnfor \tau_1\ \tau_2 & \text{types} \\
\sigma & \bnfeq & \forall \alpha. \sigma \bnfor \tau & \text{type schemes}
\end{array}
\]
Here, I use $\alpha$ to stand for any of a countably infinite set of type variables and
$H$ to stand for any type constant (including |(->)|).

Let-bound definitions in HM are assigned type schemes; lambda-bound definitions are
assigned monomorphic types, only. Thus, in HM, it is appropriate to have a function
|length :: forall a. [a] -> Int| but disallowed to have one like
|bad :: (forall a. a -> a -> a) -> Int|: |bad|'s type has a |forall| somewhere other
than at the top of the type. This type is of the second rank, and is forbidden in HM.

On the other hand, today's GHC allows types of arbitrary rank. Though a full
example of the usefulness of this ability would take us too far afield,
\citet{syb} and \citet{boxes-go-bananas} (among others) make critical use of
this ability. The cost, however, is that higher-rank types cannot be inferred.
For this reason, the following code
%
\begin{code}
higherRank x = (x True, x (5 :: Int))
\end{code}
will not compile without a type signature. Without the signature, GHC tries
to unify the types |Int| and |Bool|, failing. However, providing a signature
\begin{code}
higherRank :: (forall a. a -> a) -> (Bool, Int)
\end{code}
does the trick nicely.

Type inference in the presence of higher-rank types is well studied, and can
be made practical via bidirectional type-checking~\cite{practical-type-inference,
simple-bidirectional}.

\section{Scoped type variables}
A modest, but subtle, extension in GHC is \ext{ScopedTypeVariables}, which allows
a programmer to refer back to a declared type variable from within the body of a
function. As dealing with scoped type variables can be a point of confusion for
Haskell type-level programmers, I include a discussion of it here.

Consider this implementation of the left fold |foldl|:
\begin{code}
foldl :: (b -> a -> b) -> b -> [a] -> b
foldl f z0 xs0 = lgo z0 xs0
  where
    lgo z []      = z
    lgo z (x:xs)  = lgo (f z x) xs
\end{code}
It can be a little hard to see what is going on here, so it would be helpful
to add a type signature to the function |lgo|, thus:
\begin{spec}
    lgo :: b -> [a] -> b
\end{spec}
Yet, doing so leads to type errors. The root cause is that the |a| and |b| in
|lgo|'s type signature are considered independent from the |a| and |b| in |foldl|'s
type signature. It is as if we've assigned the type |b0 -> [a0] -> b0| to |lgo|.
Note that |lgo| uses |f| in its definition. This |f| is a parameter
to the outer |foldl|, and it has type |b -> a -> b|. When we call |f z x| in |lgo|,
we're passing |z :: b0| and |x :: [a0]| to |f|, and type errors ensue.

To make the |a| and |b| in |foldl|'s signature be lexically scoped, we simply
need to quantify them explicitly. Thus, the following gets accepted:
%{
%if style == newcode
%format foldl = foldl2
%endif
\begin{code}
foldl :: forall a b. (b -> a -> b) -> b -> [a] -> b
foldl f z0 xs0 = lgo z0 xs0
  where
    lgo :: b -> [a] -> b
    lgo z []      = z
    lgo z (x:xs)  = lgo (f z x) xs
\end{code}
%}
Another particular tricky point around \ext{ScopedTypeVariables} is that GHC
will not warn you if you are missing this extension.

\section{Functional dependencies}
Although this dissertation does not dwell much on functional dependencies, I include
them here for completeness.

Functional dependencies are GHC's earliest feature introduced to enable rich type-level
programming~\cite{fundeps,fundeps-chr}. They are, in many ways, a competitor to type families.
With functional dependencies, we can declare that the choice of one parameter to a type class
fixes the choice of another parameter. For example:
\begin{code}
class Pred (a :: Nat) (b :: Nat) | a -> b
instance Pred !Zero      !Zero
instance Pred (!Succ n)  n
\end{code}
In the declaration for class |Pred| (``predecessor''), we say that the first parameter, |a|,
determines the second one, |b|. In other words, |b| has a functional dependency on |a|.
The two instance declarations respect the functional dependency, because there are no
two instances where the same choice for |a| but differing choices for |b| could be made.

Functional dependencies are, in some ways, more powerful than type families. For
example, consider this definition of |Plus|:
\begin{code}
class Plus (a :: Nat) (b :: Nat) (r :: Nat) | a b -> r, r a -> b
instance                Plus  !Zero      b  b
instance Plus a b r =>  Plus  (!Succ a)  b  (!Succ r)
\end{code}
The functional dependencies for |Plus| are more expressive than what we can do
for type families. (However, see the work of\citet{injective-type-families},
which attempts to close this gap.) They say that |a| and |b| determine |r|,
just like the arguments to a type family determine the result, but also that
|r| and |a| determine |b|. Using this second declared functional dependency,
if we know |Plus a b r| and |Plus a b' r|, we can conclude $|b| = |b'|$.
Although the functional dependency |r b -> a| also holds, GHC is unable to
prove this.

Functional dependencies have enjoyed a rich history of aiding type-level programming~\cite{faking-it, hlist, instant-insanity}. Yet, they require a different paradigm to much of
functional programming. When writing term-level definitions, functional programmers
think in terms of functions that take a set of arguments and produce a result. Functional
dependencies, however, encode type-level programming through relations, not
proper functions. Though both functional dependencies and type families have their
proper place in the Haskell ecosystem, I have followed the path taken by other
dependently typed languages and use type-level functions as the main building blocks
of Dependent Haskell, as opposed to functional dependencies.

%%  LocalWords:  newcode rae fmt ByteArray Exts endif cha app MyShow myShow
%%  LocalWords:  smooshList xs ShowDict MkShowDict showMethod showBool poly
%%  LocalWords:  showDictBool useF MkArrayBool MkArrayInt unityped Succ MkT
%%  LocalWords:  PolyKinds fprint showSomething heteroList printList ghci HM
%%  LocalWords:  putStrLn Refl syb higherRank ScopedTypeVariables foldl lgo
%%  LocalWords:  Pred
