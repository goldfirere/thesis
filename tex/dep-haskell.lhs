%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}
import GHC.TypeLits ( type (-) )
import Prelude hiding ( replicate )
import Unsafe.Coerce
\end{code}

%endif

\chapter{Dependent Haskell}
\label{cha:dep-haskell}

This chapter lays out the differences between the Haskell of today and
Dependent Haskell. The most important distinction is the introduction
of more quantifiers, which we will study first.

\section{Quantifiers}

A \emph{quantifier} is a type-level operator that introduces the type of an
abstraction, or function. In Dependent Haskell, there are three essential
properties of quantifiers, each of which can vary independently of the others.
To understand the range of quantifiers that the language offers, we must
go through each of these properties. In the text that follows, I use the
term \emph{quantifiee} to refer to the argument quantified over. The
\emph{quantifier body} is the type ``to the right'' of the quantifier.

\subsection{Dependency}

A quantifier may be either dependent or non-dependent. A dependent quantifiee
may be used in the quantifier body; a non-dependent quantifiee may not.

Today's Haskell uses |forall| for dependent quantification, as follows:
\begin{code}
id :: forall a. a -> a
\end{code}
In this example, |a| is the quantifiee, and |a -> a| is the quantifier body.
Note that |a| is used in the quantifier body.

The normal function arrow |(->)| is an example of a non-dependent quantifier.
Consider the predecessor function:
\begin{code}
pred :: Int -> Int
\end{code}
The |Int| quantifiee is not named in the type, nor is it mentioned in the
quantifier body.

Dependent Haskell adds a new dependent quantifier, |pi|, as discussed below.

A key requirement of dependent arguments -- that is, concrete choices of
instantiations of dependent quantifiees -- is that they are expressible
in types. See \pref{sec:shared-subset} for a discussion of how this plays
out in practice.

\subsection{Relevance}
\label{sec:relevance}

A quantifier may be either relevant or irrelevant. A relevant quantifiee
may be used in a relevant position in the \emph{function} quantified over;
an irrelevant quantifiee may be used only in irrelevant positions. Note
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
here is the body of |id|:
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

A quantifier may be either visible or invisible. The argument used to instantiate
a visible quantifiee appears in the Haskell source; the argument used to
instantiate an invisible quantifiee is elided. Some readers may prefer the
terms \emph{explicit} and \emph{implicit} to describe visibility; however,
these terms are sometimes used in the literature when talking about erasure
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
All arguments are always ``visible'' in System FCD.

\subsubsection{Invisibility in other languages}

\begin{noproposal}
\begin{itemize}
%{
%format dbo = "\{\!\{"
%format dbc = "\}\!\}"
\item In Agda, an argument in single braces |{ ... }| is invisible and is
instantiated via unification. An argument in double braces |dbo ... dbc| is
invisible and is instantiated by looking for an in-scope variable of the
right type. One Agda encoding of, say, the |Show| class and its |Show Bool|
instance would be to make |Show| a record containing a |show| field (much
like GHC's dictionary for |Show|) and a top-level variable of type |Show Bool|.
The lookup process for |dbo ... dbc| arguments would then find this top-level
variable.

Thus, |show|'s type in Agda might look like |forall {a} -> dbo Show a dbc -> a ->
String|.
%}
%{
%format proof = "\keyword{proof}"
%format trivial = "\keyword{trivial}"
%format auto = "\keyword{auto}"
\item Idris supports type classes in much the same way as Haskell. A constraint
listed before a |(=>)| is solved just like a Haskell type class is. However,
other invisible arguments can also have custom solving tactics. An Idris
argument in single braces |{ ... }| is solved via unification, just like in
Agda. But a programmer may insert a proof script in the braces as well to
trigger that proof script whenever the invisible parameter needs to be
instantiated. For example, a type signature like
|func : {default proof { trivial } pf : tau } -> ...| names a (possibly-dependent)
parameter |pf|, of type |tau|. When |func| is called, Idris will run the
|trivial| tactic to solve for a value of type |tau|. This value will then
be inserted in for |pf|. Because a default proof script of |trivial| is so
common, Idris offers an abbreviation |auto| which means |default proof { trivial }|.
%}
\item
Coq has quite a different view of invisible arguments than do Dependent Haskell,
Agda, or Idris. In all three of those languages, the visibility of an argument
is part of a type. In Coq, top-level directives allow the programmer to change
the visibility of arguments to already-defined functions. For example, if we
have the definition
%{
%format Definition = "\keyword{Definition}"
%format Arguments = "\keyword{Arguments}"
%format Set = "\keyword{Set}"
%format Implicit = "\keyword{Implicit}"
%format mytrue1
%format mytrue2
%format forall = "\keyword{forall}"
\begin{spec}
Definition id A (x : A) := x.
\end{spec}
(without having used |Set Implicit Arguments|) both the |A| and |x| parameters
are visible. Thus the following line is accepted:
\begin{spec}
Definition mytrue1 := id bool true.
\end{spec}
However, we can now change the visibility of the arguments to |id| with the
directive
\begin{spec}
Arguments id {A} x.
\end{spec}
allowing the following to be accepted:
\begin{spec}
Definition mytrue2 := id true.
\end{spec}

Although Coq does not allow the programmer to specify an instantiation technique
for invisible arguments, it does allow the programmer to specify whether or
not invisible arguments should be \emph{maximally inserted}. A maximally
inserted invisible argument is instantiated whenever possible; a non-maximally
inserted argument is only instantiated when needed. For example, if the |A|
argument to |id| were invisible and maximally inserted, then any use of |id|
would immediately try to solve for |A|; if this were not possible, Coq would
report a type error. If |A| were not maximally inserted, than a use of |id|
would simply have the type |forall A, A -> A|, with no worry about invisible
argument instantiation.

The issue of maximal insertion in Dependent Haskell is solved via its
bidirectional type system. See \pref{sec:bidirectional-type-system} for
the details.
%}

\end{itemize}
\end{noproposal}
\subsubsection{Visibility overrides}

\begin{noproposal}
It is often desirable when using rich types to override a declared visibility
specification. That is, when a function is declared to have an invisible
parameter |a|, a call site may wish to instantiate |a| visibly. Conversely,
a function may declare a visible parameter |b|, but a caller knows that the
choice for |b| can be discovered by unification and so wishes to omit it
at the call site.

\paragraph{Instantiating invisible parameters visibly}
Dependent Haskell introduces the new syntax |@...| to instantiate an invisible
parameter visibly. Continuing our example with |id|, we could write |id ^^ @Bool
True| instead of |id True|. This syntax works in patterns, expressions, and
types. In patterns, the choice of |@| conflicts with as-patterns, such as
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
data Nat = Zero | Succ Nat
type instance FromNat n = U n
type family U n where
  U 0 = !Zero
  U n = !Succ (U (n-1))
data Vec :: * -> Nat -> * where
  Nil  :: Vec a !Zero
  (:>) :: a -> Vec a n -> Vec a (!Succ n)
infixr 5 :>

data SNat :: Nat -> * where
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
reported; the error report is that of a typed hole.
\end{noproposal}

\subsection{The six quantifiers of Dependent Haskell}

\begin{table}
\begin{center}
\begin{tabular}{rccc}
\multicolumn{1}{c}{Quantifier} & Dependency & Relevance & Visibility \\ \hline
|forall (a :: tau). ...| & dependent & irrelevant & invisible (unification)\\
|forall (a :: tau) -> ...| & dependent & irrelevant & visible \\
|pi (a :: tau). ...| & dependent & relevant & invisible (unification) \\
|pi (a :: tau) -> ...| & dependent & relevant & visible \\
|tau => ...| & non-dependent & relevant & invisible (solving) \\
|tau -> ...| & non-dependent & relevant & visible \\
\end{tabular}
\end{center}
\caption{The six quantifiers of Dependent Haskell}
\label{tab:quantifiers}
\end{table}

Now that we have enumerated the quantifier properties, we are ready to
describe the six quantifiers that exist in Dependent Haskell. They
appear in \pref{tab:quantifiers}. The first one (|forall (a :: t). ...|)
and the last two (|=>| and |->|) exist in today's Haskell and are completely
unchanged. Dependent Haskell adds a visible |forall| and the two |pi|
quantifiers.\footnote{The choice of syntax here is directly due to the
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
Roles and dependent types have a tricky interaction, the details of which
are beyond the scope of this proposal. One approach to combining the two
features appears in a recent draft paper~\cite{equalities}. The user-facing
effects of the interaction between roles and dependent types will appear
in this section.
\end{proposal}

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

%%  LocalWords:  newcode rae fmt TypeLits endif quantifiee pred outsidein FCD
%%  LocalWords:  mytrue bool Vec theSimons FromNat Succ infixr SNat SZero Num
%%  LocalWords:  SSucc fromInteger unsafeCoerce abs signum MkAge newtype frob
%%  LocalWords:  gundry
