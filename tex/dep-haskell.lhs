%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}
import GHC.TypeLits ( type (-), TypeError, ErrorMessage(..) )
import qualified Prelude as P
import Prelude ( Num, Int, String, Either(..), (-), fromInteger, undefined,
                 Bool(..), Maybe(..), (==) )
import GHC.Exts ( fromString )
import Unsafe.Coerce
import Data.Kind ( Type )
import Data.Singletons.Prelude
import Data.Singletons.TH hiding ( (:~:)(..) )

\end{code}

%endif

\chapter{Dependent Haskell}
\label{cha:dep-haskell}


This chapter provides an overview of Dependent Haskell.
I will review the new
features of the type language (\pref{sec:new-type-features}), introduce
the small menagerie of quantifiers available in Dependent Haskell
(\pref{sec:quantifiers}), explain pattern matching in the presence
of dependent types
(\pref{sec:pattern-matching}), and conclude the chapter by
discussing several further points of interest in the design of the language.

There are many examples throughout this chapter, building on
the following definitions:
\begin{code}
-- Length-indexed vectors, from \pref{sec:length-indexed-vectors}
data Nat = Zero | Succ Nat
data Vec :: Type -> Nat -> Type where
  Nil   ::  Vec a !Zero
  (:>)  ::  a -> Vec a n -> Vec a (!Succ n)
infixr 5 :>

-- Propositional equality, from \pref{sec:prop-equality}
data a :~: b where
  Refl :: a :~: a

-- Heterogeneous lists, indexed by the list of types of elements
data HList :: [Type] -> Type where
  HNil   :: HList ![]
  (:::)  :: h -> HList t -> HList (h !: t)
infixr 5 :::
\end{code}

\section{Dependent Haskell is dependently typed}
\label{sec:new-type-features}
The most noticeable change when going from Haskell to Dependent Haskell
is that the latter is a full-spectrum dependently typed language.
Expressions and types intermix. This actually is not too great a shock
to the Haskell programmer, as the syntax of Haskell expressions and Haskell
types is so similar. However, by utterly dropping the distinction, Dependent
Haskell has many more possibilities in types, as seen in the last chapter.

\paragraph{No distinction between types and kinds}
The kind system of GHC~7.10 and earlier is described in
\pref{sec:old-kinds}. It maintained a distinction between types, which
classify terms, and kinds, which classify types. \citet{promotion}
enriched the language of kinds, allowing for some types to be promoted
into kinds, but it did not mix the two levels.

My prior work~\cite{nokinds} goes one step further than \citet{promotion}
and \emph{does} merge types with kinds by allowing non-trivial equalities
to exist among kinds. See my prior work for the details; this feature
does not come through saliently in this dissertation, as I never consider
any distinction between types and kinds.
It is this work that is implemented
and released
in GHC~8. Removing the distinction between types and kinds has opened up
new possibilities to the Haskell programmer. Below are brief examples
of these new capabilities:
\begin{itemize}
\item \emph{Explicit kind quantification}. Previously, kind variables
were all quantified implicitly. GHC~8 allows explicit kind quantification:
\begin{working}
\begin{code}
data Proxy k (a :: k) = Proxy  
  -- NB: |Proxy| takes both kind and type arguments
f :: forall k (a :: k). Proxy k a -> ()
\end{code}
\end{working}

\item \emph{Kind-indexed GADTs}. Previously, a GADT could vary the return
types of constructors only in its type variables, never its kind variables;
this restriction is lifted.
Here is a contrived example:
\begin{working}
\begin{code}
data G (a :: k) where
  MkG1 :: G Int
  MkG2 :: G Maybe
\end{code}
\end{working}
Notice that |Int| and |Maybe| have different kinds, and thus that the
instantiation of the |G|'s |k| parameter is non-uniform between
the constructors. Some recent prior work~\cite{typerep} explores 
applying a kind-indexed to enabling dynamic types within Haskell.

\item \emph{Universal promotion}. As outlined by \citet[Section 3.3]{promotion},
only some types were promoted to kinds in GHC~7.10 and below. In contrast,
GHC~8 allows all types to be used in kinds. This includes type synonyms
and type families, allowing computation in kinds for the first time.

\item \emph{GADT constructors in types}. A constructor for a GADT packs
an equality proof, which is then exposed when the constructor is matched
against. Because GHC~7.10 and earlier lacked informative equality proofs
among kinds, GADT constructors could not be used in types. (They were
simply
not promoted.) However, with the rich kind equalities permitted in
GHC~8, GADT constructors can be used freely in types, and type families
may perform GADT pattern matching.
\end{itemize}

\paragraph{Expression variables in types}
Dependent Haskell obviates the need for most closed type families by allowing
the use of ordinary functions directly in types. Because Haskell has a separate
term-level namespace from its type-level namespace, any term-level definition
used in a type must be prefixed with a |!| mark. This expands the use of a
|!| mark to promote constructors as initially introduced by \citet{promotion}.
For example:
%format !+ = "\mathop{\tick{+}}"
\begin{notyet}
\begin{spec}
(+) :: Nat -> Nat -> Nat
Zero    +  m  =  m
Succ n  +  m  =  Succ (n + m)

append :: Vec a n -> Vec a m -> Vec a (n !+ m)
append Nil       v  =  v
append (h :> t)  v  =  h :> (append t v)
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
type family n + m where
  !Zero + m = m
  !Succ n + m = !Succ (n + m)
append :: Vec a n -> Vec a m -> Vec a (n + m)
append Nil v = v
append (h :> t) v = h :> (append t v)
\end{code}
%endif
Note that this ability does not eliminate all closed type families, as
term-level function definitions cannot use non-linear patterns, nor can
they perform unsaturated matches (see \pref{sec:unsaturated-match-example}).

\paragraph{Type names in terms}
It is sometimes necessary to go the other way and mention a type when
writing something that syntactically appears to be a term. For the same
reasons we need |!| when using a term-level name in a type, we use
|^| to use a type-level name in a term. A case in point is the code
appearing in \pref{sec:type-in-term}.

\paragraph{Pattern matching in types}
It is now possible to use |case| directly in a type:
\begin{notyet}
\begin{spec}
tailOrNil :: Vec a n -> Vec a  (case n of
                                  !Zero     -> !Zero
                                  !Succ n'  -> n')
tailOrNil Nil       = Nil
tailOrNil (_ :> t)  = t
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
type family PredOrZero n where
  PredOrZero !Zero = !Zero
  PredOrZero (!Succ n) = n

tailOrNil :: Vec a n -> Vec a (PredOrZero n)
tailOrNil Nil = Nil
tailOrNil (_ :> t) = t
\end{code}
%endif

\paragraph{Anonymous functions in types}
Types may now include $\lambda$-expressions:
\begin{notyet}
\begin{spec}
eitherize :: HList types -> HList (!map (\ ty -> Either ty String) types)
eitherize HNil       =  HNil
eitherize (h ::: t)  =  Left h ::: eitherize t
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
type Eitherize t = Either t String
$(genDefunSymbols [''Eitherize])
eitherize :: HList types -> HList (Map EitherizeSym0 types)
eitherize HNil = HNil
eitherize (h ::: t) = Left h ::: eitherize t
\end{code}
%endif

\paragraph{Other expression-level syntax in types}
Having merged types and expressions, \emph{all} expression-level syntax
is now available in types (for example, |do|-notation, |let| bindings,
even arrows~\cite{arrows}). From a compilation standpoint, supporting
these features is actually not a great challenge (once we have
Chapters~\ref{cha:pico} and \ref{cha:type-inference} implemented);
it requires only interleaving type-checking with desugaring.\footnote{GHC
currently type-checks the Haskell source directly, allowing it to produce
better error messages. Only after type-checking and type inference does
it convert Haskell source into its internal language, the process
called \emph{desugaring}.} When a type-level use of elaborate expression-level
syntax is encountered, we will need to work with the desugared version,
hence the interleaving.

\section{Quantifiers}
\label{sec:quantifiers}

Beyond simply allowing old syntax in new places, as demonstrated above,
Dependent Haskell also introduces new quantifiers that allow users to write
a broader set of functions than was previously possible. Before looking at
the new quantifiers of Dependent Haskell, it is helpful to understand the
several axes along which quantifiers can vary in the context of today's
Haskell.

In Haskell,
a \emph{quantifier} is a type-level operator that introduces the type of an
abstraction, or function. In Dependent Haskell, there are four essential
properties of quantifiers, each of which can vary independently of the others.
To understand the range of quantifiers that the language offers, we must
go through each of these properties. In the text that follows, I use the
term \emph{quantifiee} to refer to the argument quantified over. The
\emph{quantifier body} is the type ``to the right'' of the quantifier.
The quantifiers introduced in this section are summarized in
\pref{fig:quantifiers}.

\subsection{Dependency}

A quantifiee may be either dependent or non-dependent. A dependent quantifiee
may be used in the quantifier body; a non-dependent quantifiee may not.

Today's Haskell uses |forall| for dependent quantification, as follows:
\begin{code}
id :: forall a. a -> a
\end{code}
In this example, |a| is the quantifiee, and |a -> a| is the quantifier body.
Note that the quantifiee |a| is used in the quantifier body.

The normal function arrow |(->)| is an example of a non-dependent quantifier.
Consider the predecessor function:
\begin{code}
pred :: Int -> Int
\end{code}
The |Int| quantifiee is not named in the type, nor is it mentioned in the
quantifier body.

In addition to |forall|, Dependent Haskell adds a new dependent quantifier,
|pi|. The only difference between |pi| and |forall| is that |pi|-quantifiee
is relevant, as we'll explore next.

\subsection{Relevance}
\label{sec:relevance}

A quantifiee may be either relevant or irrelevant. A relevant quantifiee
may be used anywhere in the function quantified over;
an irrelevant quantifiee may be used only in irrelevant positions---that is,
as an irrelevant argument to other functions or in type annotations. Note
that relevance talks about usage in the function quantified over, not the
type quantified over (which is covered by the \emph{dependency}
property).

Relevance is very closely tied to type erasure. Relevant arguments in terms
are precisely those arguments that are not erased. However, the \emph{relevance}
property applies equally to type-level functions, where erasure does not
make sense, as all types are erased. For gaining an intuition about relevance,
thinking about type erasure is a very good guide.

Today's Haskell uses |(->)| for relevant quantification. For example, here
is the body of |pred|:
\begin{code}
pred x = x-1
\end{code}
Note that |x|, a relevant quantifiee, is used in a relevant position on the
right-hand side. Relevant positions include all places in a term or type that
are not within a type annotation, other type-level context, or irrelevant
argument context, as will be
demonstrated in the next example.

Today's Haskell uses |forall| for irrelevant quantification. For example,
here is the body of |id| (as given a type signature above):
\begin{code}
id x = (x :: a)
\end{code}
The type variable |a| is the irrelevant quantifiee. According to Haskell's
scoped type variables, it is brought into scope by the |forall a| in |id|'s
type annotation. (It could also be brought into scope by using |a| in a
type annotation on the pattern |x| to the left of the |=|.) Although |a|
is used in the body of |id|, it is used only in an irrelevant position, in the
type annotation for |x|. It would violate the irrelevance of |forall| for |a|
to be used outside of a type annotation or other irrelevant context. As functions
can take irrelevant arguments, irrelevant contexts include these irrelevant
arguments.

Dependent Haskell adds a new relevant quantifier, |pi|. The fact that |pi|
is both relevant and dependent is the very reason for |pi|'s existence!

\subsection{Visibility}
\label{sec:visibility}
\label{sec:dep-haskell-vis}

A quantifiee may be either visible or invisible. The argument used to instantiate
a visible quantifiee appears in the Haskell source; the argument used to
instantiate an invisible quantifiee is elided. 

Today's Haskell uses |(->)| for visible quantification. That is, when we
pass an ordinary function an argument, the argument is visible in the
Haskell source. For example, the |3| in |pred 3| is visible.

On the other hand, today's |forall| and |(=>)| are invisible quantifiers.
When we call |id True|, the |a| in the type of |id| is instantiated at
|Bool|, but |Bool| is elided in the call |id True|. During type inference,
GHC uses unification to discover that the correct argument to use for
|a| is |Bool|.

Invisible arguments specified with |(=>)| are constraints. Take, for example,
|show :: forall a. Show a => a -> String|. The |show| function properly takes
3 arguments: the |forall|-quantified type variable |a|, the |(=>)|-quantified
dictionary for |Show a| (see \pref{sec:type-classes} if this statement
surprises you), and the |(->)|-quantified argument of type |a|. However,
we use |show| as, say, |show True|, passing only one argument visibly.
The |forall a| argument is discovered by unification to be |Bool|, but the
|Show a| argument is discovered using a different mechanism: instance solving
and lookup. (See the work of \citet{outsidein} for the algorithm used.)
We thus must be aware that invisible arguments may use different mechanisms
for instantiation.

Dependent Haskell offers both visible and invisible forms of |forall| and
|pi|; the invisible forms instantiate only via unification. Dependent Haskell
retains, of course, the invisible quantifier |(=>)|, which is instantiated
via instance lookup and solving.
Finally, note that visibility is a quality only of source Haskell.
All arguments are always ``visible'' in \pico/.

It may be helpful to compare Dependent Haskell's treatment of visibility
to that in other languages; see \pref{sec:vis-other-lang}.

\subsubsection{Visibility overrides}
\label{sec:visible-type-pat}

It is often desirable when using rich types to override a declared visibility
specification. That is, when a function is declared to have an invisible
parameter |a|, a call site may wish to instantiate |a| visibly. Conversely,
a function may declare a visible parameter |b|, but a caller knows that the
choice for |b| can be discovered by unification and so wishes to omit it
at the call site.

\paragraph{Instantiating invisible parameters visibly}
Dependent Haskell adopts the $\at\ldots$ syntax of \citet{visible-type-application} to instantiate any invisible
parameter visibly, whether it is a type or not.
Continuing our example with |id|, we could write |id (at Bool)
True| instead of |id True|. This syntax works in patterns, expressions, and
types. In patterns, the choice of $\at$ conflicts with as-patterns, such as
using the pattern |list@(x:xs)| to bind |list| to the whole list while
pattern matching. However, as-patterns are almost always written without
whitespace. I thus use the presence of whitespace before the |@| to signal
the choice between an as-pattern and a visibility override.\footnote{This
perhaps-surprising decision based on whitespace is regrettable, but it has
company. The symbol |dollar| can mean an ordinary, user-defined operator when it
is followed by a space but a Template Haskell splice when there is no space.
The symbol |.| can mean an ordinary, user-defined operator when it is
preceded by a space but indicate namespace resolution when it is not. Introducing
these oddities seems a good bargain for concision in the final language.}
Dictionaries cannot be named in Haskell, so this visibility override skips
over any constraint arguments.

\paragraph{Omitting visible parameters}
The function |replicate :: pi (n :: Nat) -> a -> Vec a n| from
\pref{sec:replicate-example} creates a length-indexed vector of length
|n|, where |n| is passed in as the first visible argument. (The true
first argument is |a|, which is invisible and elided from the type.)
However, the choice for |n| can be inferred from the context. For example:
\begin{notyet}
\begin{code}
theSimons :: Vec String (FromNat 2)
theSimons = replicate 2 "Simon"
\end{code}
\end{notyet}
%if style == newcode
\begin{code}
type instance FromNat n = U n
type family U n where
  U 0 = !Zero
  U n = !Succ (U (n-1))

data SNat :: Nat -> Type where
  SZero :: SNat !Zero
  SSucc :: SNat n -> SNat (!Succ n)

instance Num (SNat n) where
  fromInteger 0 = unsafeCoerce SZero
  fromInteger n = unsafeCoerce (SSucc (fromInteger (n-1)))

  (+) = undefined
  (-) = undefined
  (*) = undefined
  abs = undefined
  signum = undefined

\end{code}
%endif
In this case, the two uses of |2| are redundant. We know from the
type signature that the length of |theSimons| should be 2. So we can omit
the visible parameter |n| when calling |replicate|:
\begin{notyet}
\begin{spec}
theSimons' :: Vec String (FromNat 2)
theSimons' = replicate _ "Simon"
\end{spec}
\end{notyet}
The underscore tells GHC to infer the missing parameter via unification.

The two overrides can usefully be combined, when we wish to infer the
instantiation of some invisible parameters but then specify the value for
some later invisible parameter. Consider, for example,
|coerce :: forall a b. Coercible a b => a -> b|. In the call |coerce (MkAge 3)|
(where we have |newtype Age = MkAge Int|),
we
can infer the value for |a|, but the choice for |b| is a mystery. We can
thus say |coerce @_ @Int (MkAge 3)|, which will convert |MkAge 3| to an
|Int|.

The choice of syntax for omitting visible parameters conflicts somewhat with
the feature of \emph{typed holes}, whereby a programmer can leave out a part
of an expression, replacing it with an underscore, and then get an informative
error message about the type of expression expected at that point in the
program. (This is not unlike Agda's \emph{sheds} feature or Idris's
\emph{metavariables} feature.) However, this is not a true conflict, as an
uninferrable omitted visible parameter is indeed an error and should be
reported; the error report is that of a typed hole. Depending on user feedback,
this override of the underscore symbol may be hidden behind a language extension
or other compiler flag.

\subsection{Matchability}
\label{sec:matchability}

Suppose we know that |f a| equals |g b|. What relationship can we conclude
about the individual pieces? In general, nothing: there is no way to reduce
|f a ~ g b| for arbitrary |f| and |g|. Yet Haskell type inference must
simplify such equations frequently. For example:
%{
%if style == newcode
%format ... = " "
\begin{code}
instance Monad Maybe where
  return = Just
\end{code}
%endif
\begin{code}
class Monad m where
  return :: a -> m a
  ...

just5 :: Maybe Int
just5 = return 5
\end{code}
%}
When calling |return| in the body of |just5|, type inference must determine
how to instantiate the call to |return|. We can see that |m a| (the return type
of |return|) must be |Maybe Int|. We surely want type inference to decide
to set |m| to |Maybe| and |a| to |Int|! Otherwise, much current Haskell
code would no longer compile.

The reason it is sensible to reduce |m a ~ Maybe Int| to |m ~ Maybe| and
|a ~ Int| is that all type constructors in Haskell are generative and
injective, according to these definitions:
\begin{definition*}[Generativity]
If |f| and |g| are \emph{generative}, then |f a ~ g b| implies
|f ~ g|.\footnote{As we see in this definition, \emph{generativity} is
really a relation between pairs of types. We can consider the type
constructors to be a set such that any pair are generative w.r.t.~the
other. When I talk about a type being generative, it is in relation to
this set.}
\end{definition*}
\begin{definition*}[Injectivity]
If |f| is \emph{injective}, then |f a ~ f b| implies |a ~ b|.
\end{definition*}
Because these two notions go together so often in the context of Haskell,
I introduce a new word \emph{matchable}, thus:
\begin{definition*}[Matchability]
A function |f| is \emph{matchable} iff it is generative and injective.
\end{definition*}
Thus, we say that all type constructors in Haskell are matchable.
Note that if |f| and |g| are matchable, then |f a ~ g b| implies
|f ~ g| and |a ~ b|, as desired.

On the other hand, ordinary Haskell functions are not, in general,
matchable. The inability to reduce |f a ~ g b| to |f ~ g| and |a ~ b|
for arbitrary functions is precisely why type families must be saturated
in today's Haskell. If they were allowed to appear unsaturated, then
the type inference algorithm could no longer assume that higher-kinded types
are always matchable,\footnote{For example, unifying |a b| with
|Maybe Int| would no longer have a unique solution.}
and inference would grind to a halt.

The solution is to separate out matchable functions from unmatchable ones,
classifying each by their own
quantifier, as described in my prior work~\cite{promoting-type-families}.

The difference already exists in today's Haskell between a matchable arrow
and an unmatchable arrow, though this difference is invisible. When we write
an arrow in a type that classifies an expression, that arrow is unmatchable.
But when we write an arrow in a kind that classifies a type, the arrow
is matchable. This is why |map :: (a -> b) -> [a] -> [b]| does \emph{not}
cleanly
promote to the type |Map :: (a -> b) -> [a] -> [b]|; if you write that
type family, it is much more restrictive than the term-level function.

The idea
of matchability also helps to explain why, so far, we have been able only
to promote data constructors into types: data constructors are matchable---this
is why pattern matching on constructors makes any sense at all. When we
promote a data constructor to a type constructor, the constructor's matchable
nature fits well with the fact that all type constructors are matchable.

Dependent Haskell thus introduces a new arrow, spelled |!->|, that classifies
matchable functions. The idea is that |!| is used to promote data constructors,
and |!->| promotes the arrow used in data constructor types.
In order to be backward compatible, types of
type constructors (as in |data Vec :: Type -> Nat -> Type|) and types of
data constructors (as in |Just :: a -> Maybe a|) can still be written with
an ordinary arrow, even though those arrows should properly be |!->|.
Along similar lines, any arrow written in a stretch of Haskell that is
lexically a kind (that is, in a type signature in a type) is interpreted as
|!->| as long as the \ext{DependentTypes} extension is not enabled.

We can now say |!map :: (a -> b) -> [a] -> [b]|, with unmatchable |->|,
and retain the flexibility we have in the expression |map|.

\subsection{The twelve quantifiers of Dependent Haskell}

\begin{figure}
\begin{center}
\begin{tabular}{rcccc}
% & \multicolumn{2}{l}{Dependency} & \multicolumn{2}{l}{Visibility} \\
\multicolumn{1}{c}{Quantifier} & Dependency & Relevance & Visibility & Matchability \\ \hline
|forall (a :: tau). ...| & dep. & irrel. & inv.~(unification) & unmatchable\\
|!forall (a :: tau). ...| & dep. & irrel. & inv.~(unification) & matchable \\
|forall (a :: tau) -> ...| & dep. & irrel. & vis. & unmatchable \\
|!forall (a :: tau) -> ...| & dep. & irrel. & vis. & matchable \\
|pi (a :: tau). ...| & dep. & rel. & inv.~(unification) & unmatchable \\
|!pi (a :: tau). ...| & dep. & rel. & inv.~(unification) & matchable \\
|pi (a :: tau) -> ...| & dep. & rel. & vis. & unmatchable \\
|!pi (a :: tau) -> ...| & dep. & rel. & vis. & matchable \\
|tau => ...| & non-dep. & rel. & inv.~(solving) & unmatchable \\
|tau !=> ...| & non-dep. & rel. & inv.~(solving) & matchable \\
|tau -> ...| & non-dep. & rel. & vis. & unmatchable \\
|tau !-> ...| & non-dep. & rel. & vis. & matchable \\
\end{tabular}
\end{center}
\caption{The twelve quantifiers of Dependent Haskell}
\label{fig:quantifiers}
\end{figure}

Now that we have enumerated the quantifier properties, we are ready to
describe the twelve quantifiers that exist in Dependent Haskell. They
appear in \pref{fig:quantifiers}. The first one (|forall (a :: t). ...|)
and two near the bottom (|=>| and |->|)
exist in today's Haskell and are completely
unchanged. Dependent Haskell adds a visible |forall|, the |pi|
quantifiers, and matchable versions of everything.\footnote{The choice of syntax here is directly due to the
work of \citet{gundry-thesis}.}

It is expected that the matchable quantifiers will be a rarity in
user code. These quantifiers are used to describe type and data constructors,
but matchability is assumed in a type or data constructor signature. Beyond
those signatures, I don't imagine many users will need to write matchable
function types. However, there is no reason to \emph{prevent} users from
writing these, so I have included them in the user-facing design.

The visible |forall| is useful in situations where a type parameter might
otherwise be ambiguous. For example, suppose |F| is a non-injective~\cite{injective-type-families}
type family and
consider this:
\begin{spec}
frob :: forall a. F a -> F [a]
\end{spec}
This type signature is inherently ambiguous---we cannot know the
choice of |a| even if we know we want |a| such that |frob :: Int -> Bool|---and GHC reports an error
when it is written. Suppose that we know we
want a particular use of |frob| to have type |Int -> Bool|. Even with
that knowledge, there is no way to determine how to instantiate |a|.
To fix this problem, we simply make |a| visible:
\begin{notyet}
\begin{spec}
frob :: forall a -> F a -> F [a]
\end{spec}
\end{notyet}
Now, any call to |frob| must specify the choice for |a|, and the type
is no longer ambiguous.

A |pi|-quantified parameter is both dependent (it can be used in types)
and relevant (it can be used in terms). Critically, pattern-matching (in a term)
on
a |pi|-quantified parameter informs our knowledge about that parameter as
it is used in types, a subject we explore in the next section.

Lastly, Dependent Haskell omits the non-dependent, irrelevant quantifiers, as
a non-dependent, irrelevant quantifiee would not be able to be used anywhere.

\section{Pattern matching}
\label{sec:pattern-matching}

We will approach an understanding of pattern matches in stages, working
through three examples of increasing complexity. All these examples will
work over the somewhat hackneyed length-indexed vectors
for simplicity and familiarity.

\subsection{A simple pattern match}
Naturally, Dependent Haskell retains the capability for simple pattern matches:
\begin{code}
-- |isEmpty :: Vec a n -> Bool|
isEmpty v = case v of
  Nil  ->  True
  _    ->  False
\end{code}
A simple pattern match looks at a \emph{scrutinee}---in this case, |v|---and
chooses a |case| alternative depending on the value of the scrutinee.
The bodies of the |case| alternatives need no extra information to be well typed.
In this case, every body is clearly a |Bool|, with no dependency on which
case has been chosen. Indeed, swapping the bodies would yield a well typed
pattern match, too. In a simple pattern match, no type signature is required.\footnote{Expert readers may be puzzled why this example is accepted without a type
signature. After all, pattern-matching against |Nil| indeed \emph{does}
introduce a type equality, making the result type of the match hard to infer.
In this case, however, the existence of the last pattern, |_|, which introduces
no equalities, allows the return type to be inferred as |Bool|.}

\subsection{A GADT pattern match}
\label{sec:safeTail}
Today's Haskell (and Dependent Haskell) supports GADT pattern-matches,
where learning about the constructor that forms a scrutinee's value can
affect the types in a |case| alternative body. Here is the example:
\begin{notyet}
\begin{spec}
pred :: Nat -> Nat
pred Zero      = error "pred Zero"
pred (Succ n)  = n

safeTail :: Vec a n -> Either (n :~: !Zero) (Vec a (!pred n))
safeTail Nil       = Left Refl
safeTail (_ :> t)  = Right t
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
type family Pred (n :: Nat) :: Nat where
  Pred !Zero = TypeError (!Text "pred Zero")
  Pred (!Succ n) = n

safeTail :: Vec a n -> Either (n :~: !Zero) (Vec a (Pred n))
safeTail Nil = Left Refl
safeTail (_ :> t) = Right t
\end{code}
%endif
In this example, we must use type information learned through the pattern
match in order for the body of the pattern match to type-check. (Here,
and in the last example, I use the more typical syntax of defining a function
via pattern matching. The reasoning is the same as if I had used an 
explicit |case|.) Let's examine the two pattern match bodies individually:
\begin{itemize}
\item For |Left Refl| to be well typed at |Either (n :~: !Zero) tau|,
we need to know that |n| is indeed |!Zero|. This fact is known only
because we have pattern-matched on |Nil|. Note that the type of
|Nil| is |Vec a !Zero|. Because we have discovered that our argument
of type |Vec a n| is |Nil :: Vec a !Zero|, it must be that |n ~ !Zero|,
as desired.
\item For |Right t| to be well typed at |Either tau (Vec a (!pred n))|
(where |t :: Vec a n'| for some |n'|), we need to know that |n ~ !Succ n'|,
so that we can simplify |!pred n| to |!pred (!Succ n')| to |n'|. The
equality |n ~ !Succ n'| is exactly what we get by pattern-matching on
|:>|.
\end{itemize}
Note that I have provided a type signature for |safeTail|. This is
necessary in the event of a GADT pattern match, because there is no
way, in general, to infer the return type of a pattern match where
each branch has a type equality in scope.\footnote{If this last
statement is a surprise to you, the introduction of
\citet{outsidein} has a nice explanation of why this is a hard problem.}

\subsection{Dependent pattern match}
\label{sec:dependent-pattern-match}

New to Dependent Haskell is the dependent pattern match, shown here:
\begin{notyet}
\begin{spec}
replicate :: pi n -> a -> Vec a n
replicate Zero       _  =  Nil
replicate (Succ n')  x  =  x :> replicate n' x
\end{spec}
\end{notyet}
%if style == newcode
\begin{code}
replicate :: SNat n -> a -> Vec a n
replicate SZero _ = Nil
replicate (SSucc n) x = x :> replicate n x
\end{code}
%endif
Let's again consider the function bodies one at a time:
\begin{itemize}
\item Its type signature tells us |Nil| has type |Vec a !Zero|. Thus
for |Nil| to be well typed in |replicate|, we must know that |n ~ !Zero|.
We indeed do know this, as we have scrutinized |n| and found that |n|
is |!Zero|.
\item For the recursive call to be well typed, we need to know that
|n ~ !Succ n'|, which is, once again, what we know by the pattern match.
\end{itemize}
Note the difference between this case of dependent pattern match and
the previous case of GADT pattern match. In GADT pattern matching,
the equality assumption
of interest is found by looking at the type of the constructor that we have
found. In a dependent pattern match, on the other hand, the equality
assumption of interest is between the scrutinee and the constructor. In
our case here, the scrutinized value is not even of a GADT; |Nat| is a
perfectly ordinary, Haskell98 datatype.

A question naturally comes up in this example: when should we do dependent
pattern match and when should we do a traditional (non-dependent)
pattern match? A naive answer might be to always do dependent pattern matching,
as we can always feel free to ignore the extra, unused equality if we do not
need it. However, this would not work in practice---with an equality assumption
in scope, we cannot accurately infer the return type of a pattern match.
Yet this last problem delivers us the solution: \emph{use dependent pattern matching
only when we know a match's result type}, as propagated down via a bidirectional
type system. (This is much the same way that today's Haskell allows inference
in the presence of higher-rank types~\cite{practical-type-inference}. See
\pref{sec:bidir-dependent-pattern-match} for the details.)
 If we know a result type and do not
need the dependent pattern match equality, no harm is done. On the other hand,
if we do not know the result type, this design decision means that
dependent pattern matching does not get in the way of inferring the types
of Haskell98 programs.

\section{Discussion}

The larger syntactic changes to Haskell as it becomes Dependent Haskell
are sketched above. In addition to these changes, Haskell's typing rules
naturally become much more involved. Though a declarative specification
remains out of reach, \pref{cha:type-inference} describes
(and \pref{app:inference-rules} details) the algorithm \bake/, which is
used to detect type-correct Dependent Haskell programs. It is important
future work to develop a more declarative specification of Dependent Haskell.

This section comments on several topics that affect the design
of Dependent Haskell.

\subsection{$\ottkw{Type} :\ottkw{Type}$}
\label{sec:type-in-type}

Dependent Haskell includes the $\ottkw{Type} : \ottkw{Type}$ axiom, avoiding
the infinite hierarchy of sorts~\cite{russell-universes,luo-ecc} that appear
in other dependently-typed languages. This choice is made solely to
simplify the language. Other languages avoid the $\ottkw{Type} : \ottkw{Type}$
axiom in order to remain consistent as a logic. However, to have logical
consistency, a language must be total. Haskell already has many sources
of partiality, so there is little risk in adding one more.

Despite the questionable reputation of the $\ottkw{Type} : \ottkw{Type}$ axiom,
languages with this feature have been proved type-safe for some time.
\citet{cardelli-type-in-type} gives a thorough early history of the axiom
and presents a type-safe language with $\ottkw{Type} : \ottkw{Type}$.
Given the inherent partiality of Haskell, the inclusion of this axiom
has little effect on the theory.

\subsection{Inferring |pi|}

The discussion of quantifiers in this chapter begs a question: which quantifier
is chosen when the user has not written any? The answer: |->|. Despite
all of the advances to the type system that come with Dependent Haskell,
the non-dependent, relevant, visible, and unmatchable function type, |->|,
remains the bedrock. In absence of other information, this is the quantifier
that will be used.

However, as determined by the type inference process (\pref{cha:type-inference}),
an inferred type might still have a |pi| in it. For example, if I declare
\begin{code}
replicate' = replicate
\end{code}
without giving a type signature to |replicate'|, it should naturally get
the same type (which includes a |pi|) as |replicate|. Indeed this is what
is delivered by \bake/, Dependent Haskell's type inference algorithm.

On the other hand, the generalized type of the expression |\f g x -> f (g x)| is
|forall a b c. (b -> c) -> (a -> b) -> (a -> c)|, the traditional type for
function composition, not the much more elaborate type (see \pref{sec:dependent-compose}) for a dependently typed composition function. The more exotic
types are introduced only when written in by the user.

\subsection{Roles and dependent types}
\label{sec:roles-and-dependent-types}

Integrating dependent types with Haskell's \emph{role}
mechanism~\cite{safe-coercions-jfp} is a challenge, as explored in some depth
in my prior, unpublished work~\cite{overabundance-of-equalities}.
Instead of addressing this issue head-on, I am deferring the resolution
until we can find a better solution than what was proposed in that prior
work. That approach, unworthy of being repeated here, is far too ornate
and hard to predict. Instead, I make a simplifying assumption that all
coercions used in types have a nominal role.\footnote{If you are not familiar
with roles, do not fret. Instead, safely skip the rest of this subsection.}
This choice restricts the way Haskell |newtype|s can work with dependent types
if the |coerce| function has been used. A violation of this restriction
(yet to be nailed down, exactly) can be detected after type-checking
and does not affect the larger type system. It is my hope that, once the
rest of Dependent Haskell is implemented, a solution to this thorny problem
will present itself. A leading, unexplored candidate is to have two
types of casts: representational and nominal. Currently, all casts
are representational; possibly, tracking representational casts separately
from nominal casts will allow a smoother integration of roles and dependent
types than does the ornate approach in my prior work.

\subsection{Impredicativity, or lack thereof}
\label{sec:impredicativity}

Despite a published paper~\cite{boxy-types} and continued attempts at
cracking this nut, GHC lacks support for impredicativity.\footnote{There does exist an extension \ext{ImpredicativeTypes}. However, it is
unmaintained, deprecated, and quite broken.}
Here, I use the following definitions in my meaning of impredicativity,
which has admittedly drifted somewhat from its philosophical origins:
\begin{definition*}[Simple types]
A \emph{simple type} has no constraint, quantification, or dependency.
\end{definition*}
\begin{definition*}[Impredicativity]
A program is \emph{impredicative} if it requires a non-simple type to
be substituted for a type variable.
\end{definition*}
Impredicativity is challenging to implement while retaining predictable
type inference, essentially because it is impossible to know where to
infer invisible arguments---invisible arguments can be hidden behind
a
type variable in an impredicative type system.

Dependent Haskell does not change this state of affairs in any way.
In Dependent Haskell, just like in today's Haskell, impredicativity
is simply not allowed.

There is a tantalizing future direction here, however: are the restrictions
around impredicativity due to invisible binders only? Perhaps. Up until now,
it has been impossible to have a dependent or irrelevant binder without
that binder also being invisible. (To wit, |forall| is the invisible,
dependent, irrelevant binder of today's Haskell.) One of the tasks of
enhancing Haskell with dependent types is picking apart the relationship
among all of the qualities of quantifiers~\cite{hasochism}. It is conceivable
that the reason impredicativity hinders the predictability of type inference
has to do only with visibility, allowing arbitrary instantiations of type
variables with complex types, as long as they have no invisible binders.
Such an idea requires close study before implementing, but by pursuing this
idea, we may be able to relax the impredicativity restriction substantially.

\subsection{Running proofs}
\label{sec:running-proofs}

Haskell is a partial language. It has a multitude of ways of introducing a
computation that does not reduce to a value: |undefined|/|error|, general
recursion, incomplete pattern matches, non-strictly-positive datatypes,
baked-in type representations~\cite{typerep}, and possibly Girard's
paradox~\cite{girard-thesis,simplification-girard-paradox}, among others.
This is in sharp contrast to many other dependently typed language, which
are total. (An important exception is Cayenne. See \pref{sec:cayenne}.)

In a total language, if you have a function |pf| that results in a proof that
|a ~ b|, you never need to run the function. (Here, I'm ignoring the possibility
of multiple, different proofs of equality~\cite{hott}.) By the totality of
that language, you are assured that |pf| will always terminate, and thus running
|pf| yields no information.

On the other hand, in a partial language like Haskell, it is always possible
that |pf| diverges or errors. We are thus required to run |pf| to
make sure that it terminates. This is disappointing, as the only point of
running |pf| is to prove a type equality, and types are supposed to be erased.
However, the Haskell function |pf| has two possible outcomes: an uninformative
(at runtime) proof of type equality, or divergence. There seems to be no easy,
sound way around this restriction, which will unfortunately have a real effect
on the runtimes of dependently typed Haskell programs.\footnote{Note that
running a term like |pf| is the \emph{only} negative consequence of Haskell's
partiality. If, say, Agda always ran its proofs, it could be partial, too!
This loses logical consistency---and may surprise users expecting something
that looks like a proof to actually be a proof---but the language would
remain type safe.}

Despite not having an easy, sound workaround, GHC already comes with an easy,
\emph{un}sound workaround: rewrite rules~\cite{rules}. A rewrite rule (written with a
|RULES| pragma) instructs GHC to exchange one fragment of a program in
its intermediate language with another, by pattern matching on the program
structure. For example, a user can write a rule to change |map id| to |id|. To
the case in point, a user could write a rule that changes |pf ...| to
|unsafeCoerce Refl|. Such a rule would eliminate the possibility of a runtime
cost to the proof. By writing this rule, the user is effectively asserting
that the proof always terminates.

\subsection{Import and export lists}

Recall the |safeTail| example from \pref{sec:safeTail}. As discussed in that section,
for |safeTail| to compile,
it is necessary to reduce |!pred (!Succ n')| to |n'|. This reduction requires knowledge
of the details of the implementation of |pred|. However, if we imagine that |pred|
is defined in another module, it is conceivable that the author of |pred| wishes
to keep the precise implementation of |pred| private---after all, it might change in
future versions of the module. Naturally, hiding the implementation of |pred| would
prevent an importing module from writing |safeTail|, but that should be the library
author's prerogative.

Another way of examining this problem is to recognize that the definition of |pred|
encompasses two distinct pieces of information: |pred|'s type and |pred|'s body.
A module author should have the option of exporting the type without the body.

%{
%format !! = " "   
% the above squelches the space between an id and the (..)
This finer control is done by a small generalization of the syntax in import and
export lists. If a user includes |pred| in an import/export list, only the name
|pred| and its type are involved. On the other hand, writing |pred !! (..)| (with a
literal |(..)| in the source code) in the
import/export list also includes |pred|'s implementation. This echoes the current
syntax of using, say, |Bool| to export only the |Bool| symbol while |Bool !! (..)|
exports |Bool| with all of its constructors.
%}

\subsection{Type-checking is undecidable}
\label{sec:type-checking-undec}

In order to type-check a Dependent Haskell program, it is sometimes necesary
to evaluate expressions used in types. Of course, these expressions might
be non-terminating in Haskell. Accordingly, type-checking Dependent Haskell
is undecidable.

This fact, however, is not worrisome. Indeed, GHC's type-checker has
had the potential to loop for some time. Assuming that the solver's own
algorithm terminates, type-checking will loop only when the user has
written a type-level program that loops. Programmers are not surprised when
they write an ordinary term-level program that loops at runtime; they
should be similarly not surprised when they write a type-level program
that loops at compile time. In order to provide a better user experience,
GHC counts reduction steps and halts with an error message if the
count gets too high; users can disable this check or increase the limit
via a compiler flag.

\section{Conclusion}

This chapter has offered a concrete description of Dependent Haskell. Other
than around the addition of new quantifiers, most of the changes are loosening
of restrictions that exist in today's Haskell. (For example, a |!| mark in a type
today can promote only a constructor; Dependent Haskell allows any identifier to
be so promoted.) Accordingly, and in concert with the conservativity of the
type inference algorithm (Sections~\ref{sec:oi} and~\ref{sec:sb}), programs that
compile today will continue to do so under Dependent Haskell.

Naturally, what is described here is just my own considered vision for Dependent
Haskell. I am looking forward to the process of getting feedback from the Haskell
community and evolving this description of the language to fit the community's
needs.

%%  LocalWords:  newcode rae fmt TypeLits endif quantifiee pred outsidein FCD
%%  LocalWords:  mytrue bool Vec theSimons FromNat Succ infixr SNat SZero Num
%%  LocalWords:  SSucc fromInteger unsafeCoerce abs signum MkAge newtype frob
%%  LocalWords:  gundry TypeError ErrorMessage Refl HList HNil tailOrNil Exts
%%  LocalWords:  PredOrZero eitherize MkG
