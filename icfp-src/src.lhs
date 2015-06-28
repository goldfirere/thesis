% -*- mode: LaTeX -*-

\documentclass[10pt,twocolumn]{article}

\usepackage{fullpage}
\usepackage[numbers]{natbib}

%include polycode.fmt
%include rae.fmt

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
\end{minipage}
%\end{@twocolumnfalse}
]
\vspace{1cm}

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

 Despite the fact that many of these are extensions to Haskell's
type system, no


\bibliographystyle{plainnat}
\bibliography{../bib/rae}

\end{document}
