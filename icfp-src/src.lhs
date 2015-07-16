% -*- mode: LaTeX -*-

\documentclass[10pt,twocolumn]{article}

\usepackage{fullpage}
\usepackage[numbers,sort&compress]{natbib}
\usepackage{hyperref}

%include polycode.fmt
%include rae.fmt

\newcommand{\outsidein}{\textsc{OutsideIn(X)}}

\begin{document}

\twocolumn[
%  \begin{@twocolumnfalse}
\begin{minipage}{\textwidth}
\begin{center}
\LARGE
Dependent Types in Haskell\\ \vspace{1ex}
\large
Richard Eisenberg\\
University of Pennsylvania\\
\texttt{eir@@cis.upenn.edu}\\
Category: graduate student\\
ACM Student Member: 1901387\\  \vspace{1ex}
%
1125 Coventry Rd.\\
Cheltenham, PA 19012\\ \vspace{1ex}
Advisor: Stephanie Weirich (\texttt{sweirich@@cis.upenn.edu})
\end{center}
\vspace{.5cm}
\end{minipage}
%\end{@twocolumnfalse}
]

Since its inception, Haskell has been a hotbed of research into programming
language design~\cite{history-of-haskell}. The Haskell core
language~\cite{haskell98} has been extended with functional
dependencies~\cite{fundeps}, type families (open~\cite{chak1,chak2},
closed~\cite{closed-type-families}, and
injective~\cite{injective-type-families}), generalized algebraic datatypes
(GADTs)~\cite{xi-gadt,gadt-type-inference}, instance
chains~\cite{instance-chains}, datatypes promoted into kinds~\cite{promotion},
a customizable way to control error messages~\cite{helium}, support for
generic programming~\cite{syb, generic-deriving}, arrows~\cite{arrows},
higher-rank types~\cite{practical-type-inference},
roles~\cite{popl-roles,safe-coercions}, and a meta-programming
facility~\cite{template-haskell}, among many other extensions. Several of
these extensions taken together (specifically: GADTs, type families, and
promoted datatypes) bring Haskell to the doorstep of dependent
types~\cite{weirich-icfp-keynote}. These extensions allow users to write
well-kinded programs in types, and have these programs interact with values
available at runtime. But Haskell is not quite dependently typed.

My work is to close
this gap, giving Haskell full dependent types and a proper $\Pi$-binder
(explained below), enabling easier and more dependently-typed programming in
Haskell. An important part of this work is implementing the support for
dependent types in the Glasgow Haskell Compiler (GHC), the main compiler for
the language.

The contributions I expect to offer from this work include the following:

\begin{itemize}
\item The design, including motivation behind decisions, of a version
of Haskell with dependent types. The extension of the language to
dependent types must remain backward-compatible with the existing Haskell
language.

\item A type inference algorithm, compatible with GHC's existing
framework, \outsidein{}~\cite{outsidein}, that will process dependent types.
The algorithm must go somewhat beyond the inference algorithms in existing
dependently typed languages (such as Idris~\cite{idris}, Agda~\cite{agda},
and Coq~\cite{coq}), due to the requirement of backward compatibility.

\item An implementation of dependently-typed Haskell in GHC.

\item Several examples of practical dependently-typed programs, including
at least one larger case study. As dependent types have remained a somewhat
esoteric feature, coming up with new applications of the technique remains
an important contribution.
\end{itemize}

\subsubsection*{Why dependent types?}
\subsubsection*{Why Haskell?}
\subsubsection*{Current status}
\subsubsection*{Related work: \citet{gundry-thesis}}
\subsubsection*{Related work: other languages}

\bibliographystyle{plainnat}
\bibliography{../bib/rae}

\end{document}
