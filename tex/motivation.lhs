%% -*- mode: LaTeX -*-

%include rae.fmt

\chapter{Motivation}

Functional programmers use dependent types in two primary ways: in order
to eliminate erroneous programs from being accepted, and in order to write
intricate programs that a simply-typed language cannot accept. In this chapter,
we will motivate the use of dependent types from both of these angles. The
chapter concludes with a section motivating why Haskell, in particular, is
ripe for dependent types.

\section{Eliminating erroneous programs}

\ifproposal
In this proposal, I elide the details of the motivating examples. Instead,
I list them as stubs to be filled out later, when writing the dissertation
proper.
\fi

\subsection{Simple example: Length-indexed vectors}

\subsection{Strongly typed lambda calculus interpreter}

\subsection{Units-of-measure}

\subsection{Machine-checked sorting algorithm}

\subsection{Type-safe database access}

See also other examples in \citet{power-of-pi} and \citet{hasochism}.

\section{Encoding hard-to-type programs}

\subsection{Variable-arity |zipWith|}

\subsection{Deconstructing runtime types}

\subsection{Inferred algebraic effects}

\cite{algebraic-effects}

\section{Why Haskell?}
