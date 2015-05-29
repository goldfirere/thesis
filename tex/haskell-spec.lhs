%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt
%endif

\chapter{A specification of Dependent Haskell}
\label{cha:haskell-spec}

\rae{Must cite \cite{static-semantics-for-haskell} and \cite{haskell-semantics}.}

\begin{proposal}
This section will lay out a formal static semantics for Haskell, including
|data| and |type family| definitions. This semantics will then be used in
\pref{cha:type-inference} as the specification for the type inference algorithm.
\end{proposal}

\section{Bidirectional type systems}
\label{sec:bidirectional-type-system}

\begin{proposal}
Critical to Dependent Haskell is its reliance on a bidirectional type
system~\cite{local-type-inference}. The bidirectional system is used to allow
higher-rank polymorphism~\cite{practical-type-inference} as well as dependent
pattern matching (\pref{sec:pattern-matching}). The presentation here
will be along the lines of that of \citet{simple-bidirectional}.
\end{proposal}

\section{Types}

\section{Terms}

\section{Type declarations}
