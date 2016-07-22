%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}
import GHC.TypeLits ( type (-), TypeError, ErrorMessage(..) )
import qualified Prelude as P
import Prelude ( Num, Int, String, Either(..), (-), fromInteger, undefined,
                 Bool(..), Maybe(..) )
import Unsafe.Coerce
import Data.Kind ( Type )
import Data.Singletons.Prelude
import Data.Singletons.TH hiding ( (:~:)(..) )

\end{code}

%endif

\chapter{Dependent Haskell}
\label{cha:dep-haskell}


This chapter provides an overview of Dependent Haskell, focusing on the
aspects of Dependent Haskell that are different from the Haskell implemented
in GHC 8 and described in \pref{cha:prelim}. I will review the new
features of the type language (\pref{sec:new-type-features}), introduce
the small menagerie of quantifiers available in Dependent Haskell
(\pref{sec:quantifiers}), explain pattern matching in the presence
of dependent types
(\pref{sec:dependent-pattern-match}), and conclude the chapter by
discussing several further points of interest in the design of the language.

There are many examples throughout this chapter, many of which depend on
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
is that the latter is, of course, a full-spectrum dependently typed language.
Expressions and types intermix. This actually is not too great a shock
to the Haskell programmer, as the syntax of Haskell expressions and Haskell
types is so similar. However, by utterly dropping the distinction, Dependent
Haskell has many more possibilities in types, as seen in the last chapter.

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
term-level function definitions cannot use non-linear patterns nor can
they perform unsaturated matches (see \pref{sec:unsaturated-match-example}).

\paragraph{Pattern matching in types}
It is now possible to use |case| directly in a type:
\begin{notyet}
\begin{spec}
tailOrNil :: Vec a n -> Vec a  (case n of
                                  Zero     -> Zero
                                  Succ n'  -> n')
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
it requires only interleaving typechecking with desugaring.\footnote{GHC
currently typechecks the Haskell source directly, allowing it to produce
better error messages. Only after typechecking and type inference does
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

A \emph{quantifier} is a type-level operator that introduces the type of an
abstraction, or function. In Dependent Haskell, there are four essential
properties of quantifiers, each of which can vary independently of the others.
To understand the range of quantifiers that the language offers, we must
go through each of these properties. In the text that follows, I use the
term \emph{quantifiee} to refer to the argument quantified over. The
\emph{quantifier body} is the type ``to the right'' of the quantifier.

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
are not within a type annotation or other type-level context, as will be
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
instantiate an invisible quantifiee is elided. Some readers may prefer the
terms \emph{explicit} and \emph{implicit} to describe visibility; however,
these terms are sometimes used in the literature (e.g.,~\cite{miquel-icc})
when talking about erasure
properties. I will stick to \emph{visible} and \emph{invisible} throughout this
dissertation.

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
via instanced lookup and solving.
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
\pref{sec:length-indexed-vectors} creates a length-indexed vector of length
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

replicate :: SNat n -> a -> Vec a n
replicate SZero _ = Nil
replicate (SSucc n) x = x :> replicate n x

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
\begin{noway}
\begin{spec}
theSimons' :: Vec String (FromNat 2)
theSimons' = replicate _ "Simon"
\end{spec}
\end{noway}
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
|f ~ g|.
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
in today's Haskell. If the were allowed to appear unsaturated, then
the type inference algorithm could no longer assume that higher-kinded types
are always matchable, and inference would grind to a halt.

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
|!->| as long as the \ext{-XDependentTypes} extension is not enabled.

We can now say |!map :: (a -> b) -> [a] -> [b]|, with unmatchable |->|,
and retain the flexibility we have in the expression |map|.

\subsection{The eleven quantifiers of Dependent Haskell}

\begin{table}
\begin{center}
\begin{tabular}{rcccc}
% & \multicolumn{2}{l}{Dependency} & \multicolumn{2}{l}{Visibility} \\
\multicolumn{1}{c}{Quantifier} & Dependency & Relevance & Visibility & Matchability \\ \hline
|forall (a :: tau). ...| & dep. & irrel. & inv. (unification) & unmatchable\\
|!forall (a :: tau). ...| & dep. & irrel. & inv. (unification) & matchable \\
|forall (a :: tau) -> ...| & dep. & irrel. & vis. & unmatchable \\
|!forall (a :: tau) -> ...| & dep. & irrel. & vis. & matchable \\
|pi (a :: tau). ...| & dep. & rel. & inv. (unification) & unmatchable \\
|!pi (a :: tau). ...| & dep. & rel. & inv. (unification) & matchable \\
|pi (a :: tau) -> ...| & dep. & rel. & vis. & unmatchable \\
|!pi (a :: tau) -> ...| & dep. & rel. & vis. & matchable \\
|tau => ...| & non-dep. & rel. & inv. (solving) & unmatchable \\
|tau -> ...| & non-dep. & rel. & vis. & unmatchable \\
|tau !-> ...| & non-dep. & rel. & vis. & matchable \\
\end{tabular}
\end{center}
\caption{The eleven quantifiers of Dependent Haskell}
\label{tab:quantifiers}
\end{table}

Now that we have enumerated the quantifier properties, we are ready to
describe the eleven quantifiers that exist in Dependent Haskell. They
appear in \pref{tab:quantifiers}. The first one (|forall (a :: t). ...|)
and the two near the bottom (|=>| and |->|)
exist in today's Haskell and are completely
unchanged. Dependent Haskell adds a visible |forall|, the |pi|
quantifiers, and matchable versions of everything save |=>|.\footnote{The choice of syntax here is directly due to the
work of \citet{gundry-thesis}.}



The visible |forall| is useful in situations where a type parameter might
otherwise be ambiguous. For example, suppose |F| is a type family and
consider this:
\begin{spec}
frob :: forall a. F a -> F [a]
\end{spec}
This type signature is inherently ambiguous, and GHC reports an error
when it is written. Suppose that we know we
want a particular use of |frob| to have type |Int -> Bool|. Even with
that knowledge, there is no way to determine how to instantiate |a|.
To fix this problem, we simply make |a| visible:
\begin{noway}
\begin{spec}
frob :: forall a -> F a -> F [a]
\end{spec}
\end{noway}
Now, any call to |frob| must specify the choice for |a|, and the type
is no longer ambiguous.

A |pi|-quantified parameter is both dependent (it can be used in types)
and relevant (it can be used in terms). Critically, pattern-matching (in a term)
on
a |pi|-quantified parameter informs our knowledge about that parameter as
it is used in types, a subject we explore next.

\section{Pattern matching}
\label{sec:pattern-matching}
\label{sec:dependent-pattern-match}

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
The bodies of the |case| alternatives need no extra information to be well-typed.
In this case, every body is clearly a |Bool|, with no dependency on which
case has been chosen. Indeed, swapping the bodies would yield a well-typed
pattern match, too. In a simple pattern match, no type signature is required.\footnote{Expert readers may be puzzled why this example is accepted without a type
signature. After all, pattern-matching against |Nil| indeed \emph{does}
introduce a type equality, making the result type of the match hard to infer.
In this case, however, the existence of the last pattern, |_|, which introduces
no equalities, allows the return type to be inferred as |Bool|.}

\subsection{A GADT pattern match}
Today's Haskell (and Dependent Haskell) supports GADT pattern-matches,
where learning about the constructor that forms a scrutinee's value can
affect the types in a |case| alternative body. Here is the example:
\rae{color?}
\begin{spec}
pred :: Nat -> Nat
pred Zero      = error "pred Zero"
pred (Succ n)  = n

safeTail :: Vec a n -> Either (n :~: !Zero) (Vec a (!pred n))
safeTail Nil       = Left Refl
safeTail (_ :> t)  = Right t
\end{spec}
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


isEmpty: simple pattern match
append: GADT pattern match
replicate: dependent pattern match


We will use |replicate| as a solid, simple example of a dependent pattern

\begin{proposal}
This section will address how dependent pattern matching works, illustrated
by examples. The key points will be
\begin{itemize}
\item A dependent pattern match is one where the term-level match also informs
a |pi|-quantified variable in types.
\item Dependent Haskell source will include only one |case| construct. Whether
or not to do dependent matching will depend on the context. Specifically,
a pattern match will be dependent iff:
\begin{enumerate}
\item The scrutinee (the expression between |case| and |of|) mentions only
  |pi|-quantified variables and expressions in the shared subset
  (\pref{sec:shared-subset}), \emph{and}
\item The result type of the pattern-match is known (via bidirectional
type inference).
\end{enumerate}
I will also explain why we need these conditions.
\end{itemize}
\end{proposal}

\section{Inferring |pi|}

\begin{proposal}
If a function is written at top-level without a signature, will it have
any |pi|-quantified parameters? At the time of writing, I think the answer
is ``no''. This section will describe inference around |pi|-quantified
parameters and will address how a user-written |\|-expression will be
treated. (My current plan: all variables bound by an explicit |\| will
be |(->)|-quantified, never |pi|-quantified.)
\end{proposal}

\section{Shared subset of terms and types}
\label{sec:shared-subset}

\begin{proposal}
Not every term can appear in a type. For example, today's Haskell does not
permit |\|, |case|, or |let| in types. Types also do not yet permit
unsaturated type functions. This section will explore the limits of what
can be expressed in both types and terms. Depending on time constraints
as I write this dissertation, I may work on expanding this subset to
include some of the constructs above. Inspiration for doing so will
come from previous work~\cite{promoting-functions-to-type-families},
which suggests that allowing \emph{universal} promotion may well be
possible.
\end{proposal}

\section{Roles and dependent types}
\label{sec:roles-and-dependent-types}

\begin{proposal}
\rae{TODO: Remove.}
Roles and dependent types have a tricky interaction, the details of which
are beyond the scope of this proposal. One approach to combining the two
features appears in a recent draft paper. The user-facing
effects of the interaction between roles and dependent types will appear
in this section.
\end{proposal}

\subsection{Dependent pattern matching}
\label{sec:dependent-pattern-matching}
\rae{TODO: Write me. Talk about bidirectionality.}

\subsection{Impredicativity, or lack thereof}
\label{sec:impredicativity}
\rae{TODO: Write me.}

\subsection{Running proofs}
\label{sec:running-proofs}
\rae{TODO: Write me.}

\section{Other syntax changes}
\subsection{Parsing for |*|}
\label{sec:parsing-star}

\subsection{Visible kind variables}
\label{sec:visible-kinds}

\begin{proposal}
Today's Haskell requires that all kind parameters always be invisible.
My work changes this, as will be discussed here.
\end{proposal}

\subsection{Import and export lists}

\begin{proposal}
If any functions are promoted into types, module writers should have the
option of whether or not to export a function's definition along with its
type. Exporting just the type will allow the function to be used in terms
and in types, but no compile-time reduction will be possible. Exporting
the full definition allows, also, compile-time reduction in types. Supporting
the choice between these export modes will require a small change to export
and import lists, as will be detailed here.
\end{proposal}

\rae{Need to define generativity and injectivity, in this chapter or elsewhere}

%%  LocalWords:  newcode rae fmt TypeLits endif quantifiee pred outsidein FCD
%%  LocalWords:  mytrue bool Vec theSimons FromNat Succ infixr SNat SZero Num
%%  LocalWords:  SSucc fromInteger unsafeCoerce abs signum MkAge newtype frob
%%  LocalWords:  gundry
