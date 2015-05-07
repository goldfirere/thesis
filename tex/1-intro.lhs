%% -*- mode: LaTeX -*-

%if style == newcode
%include rae.fmt
%endif

\chapter{Introduction}

\begin{proposal}
I have formatted this proposal as an outline of my eventual dissertation,
with drafts of parts of the final text already written.
Paragraphs rendered in blue, such as this one, are meant to appear only
in the proposal.
\end{proposal}

Haskell has become a wonderful and rich playground for type system
experimentation. Despite its relative longevity -- at 25 years
old~\cite{history-of-haskell} \rae{check!} -- type theorists still turn to
Haskell as a place to build new type system ideas and see how they work in a
practical setting~\cite{functional-dependencies, type-families, arrows, syb,
  closed-type-families, generics-with-closed-type-families, safe-coercions,
  pattern-match-and-gadts, helium-type-errors, etc}. As a result, Haskell's type system has grown
ever more intricate over the years. As the power of types in Haskell has
increased, Haskellers have started to integrate dependent types into their
programs~\cite{singletons, hasochism, she, clash, vinyl}, despite the fact
that today's Haskell\footnote{Throughout this dissertation, a reference to
  ``today's Haskell'' refers to the language implemented by the Glasgow
  Haskell Compiler (GHC), version 7.10, released in 2015.} does not internally
support dependent types. Indeed, the desire to program in Haskell but with
support for dependent types influenced the creation of Agda~\cite{agda} and
Idris~\cite{idris}; both are Haskell-like languages with support for full dependent
types.

This dissertation closes the gap, by adding support for dependent types into
Haskell directly. In this work, I detail both the changes to GHC's internal
language, known as System FC~\cite{system-fc}, and explain the changes to the
surface language necessary to support dependent types. Naturally, I must also
describe the elaboration from the surface language to the internal language,
including type inference. Along with the textual description contained in this
dissertation, I have also implemented support for dependent types in GHC directly;
I expect a future release of the software to include this support.
Much of my work builds upon the critical work of
\citet{gundry-thesis}; one of my chief contributions is adapting his work
to work with the GHC implementation and futher features of Haskell.

Specifically, I offer the following contributions:
\begin{itemize}
\item \pref{cha:motivation} includes a series of examples of dependently
  typed programming in Haskell. Though a fine line is hard to draw, these
  examples are divided into two categories: programs where rich types give a
  programmer more compile-time checks of her algorithms, and programs where
  rich types allow a programmer to express a more intricate algorithm that
  may not be well-typed under a simpler system. \pref{sec:why-haskell} then
  argues why dependent types in Haskell, in particular, are an interesting
  and worthwhile subject of study.

Although no new results, as such, are presented in \pref{cha:motivation},
gathering these examples together is a true contribution of this dissertation.
At the time of writing, dependent types are still rather esoteric in the
functional programming community, and examples of how dependent types can
do real work (outside of theorem-proving, which is beyond the scope of
dependent types in Haskell -- see \pref{sec:no-proofs}) are hard to come by.

\item \pref{cha:system-fc} is a thorough treatment of System FC, as it
has inspired today's GHC. Though there are many publications on System
FC~\cite{system-fc,etc}, it has evolved much over the years and benefits
from a solid, full treatment. Having a record of today's System FC also
allows readers to understand the extensions I add in context.

This chapter, however, does not prove
type safety of this language, deferring the proof to the system that
includes dependent types.

\item \pref{cha:dep-haskell} presents Dependent Haskell, the language
I have designed in this dissertation. This chapter is written to be useful
to practitioners, being a user manual of sorts of the new features. In
combination with \pref{cha:motivation}, this chapter could serve to educate
Haskellers on how to use the new features.

\item \pref{cha:fcd} describes System FC with dependent types,
which I have named System FCD. System FCD is an extension on System FC,
with two major changes:
\begin{enumerate}
\item System FCD supports first-class equalities among the kinds that classify
the system's types, whereas System FC supports only \emph{type} equalities.
Adding kind equalities is made simpler by also adding the \emph{Type-in-Type}
axiom (or |* :: *|) and merging the grammar of types and kinds. This aspect
of System FCD was originally presented in \citet{nokinds}.
\item System FCD also contains a proper $\Pi$-type, which quantifies over
an argument made available in both a type and a term. It is the existence
of $\Pi$-types that enables me to claim that the language is dependently
typed.
\end{enumerate}
This chapter contains the full prose and technical description of System FCD
and well as a proof of type safety (though the details of many proofs are
relegated to \pref{app:fc}).

\item \pref{cha:haskell-spec} introduces a specification of the Dependent Haskell
surface language. Though much formal work has been done on System FC --
the \emph{internal} language -- there is much less formal work done on
Haskell itself. This chapter builds a specification of the surface language,
to be used when discussing type inference and elaboration into System FCD.

\item \pref{cha:type-inference} presents the type inference and elaboration
  algorithm from Dependent Haskell to System FCD. As compared to Gundry's
  work~\cite{gundry-thesis}, the chief novelty here is that it adapts the type
  inference algorithm to work with (a slight variant of) the \outsidein/
  algorithm~\cite{outsidein}. This chapter contains proofs of soundness with
  respect both to the Haskell specification and System FCD. The inference
  algorithm is not complete, however, though I do prove completeness for
  subsets of Haskell. This lack of completeness follows directly from the
  lack of completeness of \outsidein/. See \pref{sec:incomplete} for more
  details.

\item \pref{cha:implementation} considers some of the implementation
challenges inherent in building Dependent Haskell for wide distribution.

\item \pref{cha:related} puts this work in context by comparing it to
several other dependently typed systems, both theories and implementations.
\end{itemize}

Though not a new contribution, \pref{cha:todays-haskell} contains a thorough
review of features available in today's Haskell that support dependently typed
programming. This is included as a counterpoint to the features discussed as
parts of Dependent Haskell.

With an implementation of dependent types in Haskell available, I look forward
to seeing how the Haskell community builds on top of my work and discovers
more and more applications of dependent types.
