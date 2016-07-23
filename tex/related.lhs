%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt

\begin{code}

\end{code}

%endif

\chapter{Related work}
\label{cha:related}

\section{Comparison to \citet{gundry-thesis}}

\section{Comparison to Idris}

\section{Comparison to Cayenne}
\label{sec:cayenne}
\rae{TODO: Write me.}

\begin{proposal}
Although I compare Dependent Haskell against Coq, Agda, and Idris throughout
this proposal, I plan on writing a more detailed comparison against just Idris
in this section, as my work is closest to what has been done in Idris, and I
think this comparison will be the most illuminating.
\end{proposal}

\section{Comparison to Liquid Haskell}

\section{Invisibility in other languages}
\label{sec:vis-other-lang}

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
bidirectional type system (\pref{sec:bidirectional}). The subsumption relation
effectively ensures that the correct number of invisible parameters are provided,
depending on the context.
%}

\end{itemize}


\section{Applicability beyond Haskell}

\begin{proposal}
The knowledge gained in adding dependent types to Haskell will translate
to other environments as well. A key example will be the thought of adding
dependent types to a variant of ML. Going the other way, I will examine
adding more programmatic features to existing dependently typed languages
(in particular, Haskell's \keyword{newtype} construct).
\end{proposal}

\section{Future work}

\begin{proposal}
Though this dissertation will deliver $\Pi$, that's not the end of the story.
Here are some questions I have that I do not expect will be answered in the
course of writing this work.
\begin{itemize}
\item How to improve error messages? While my work will strive hard not to
degrade error messages for non-dependently-typed programs, I offer no
guarantee about the quality of error messages in programs with lots of
dependent types. How can these be improved? More generally, how can error
messages be customized by programmers to fit their domain?

\item What editor support is necessary to make dependent types in Haskell
practical?

\item Are there constructs that I have been unable to promote? How can these
be made to work in types?

\item How do we optimize a dependently typed program? Ideally, a program should
be optimized to the same level whether an argument is dependent or not. However,
optimizing $\Pi$-quantified arguments will amount to proving the optimizations
correct! How do we retain runtime performance in the face of dependent types?

\item How will dependent types interact with type-checker
  plugins~\cite{type-checker-plugins}? Can we use an SMT solver to make working
  with dependent types easier?

\item Dependent types will allow for proper dependent pairs ($\Sigma$-types).
  Is it worth introducing new syntax to support these useful constructs directly?
\end{itemize}
\end{proposal}

%%  LocalWords:  gundry newtype SMT
