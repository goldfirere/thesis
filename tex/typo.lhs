%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%if style == newcode
%include rae.fmt
%endif

\chapter{Typographical conventions}
\label{app:typo}

This dissertation is typeset using \LaTeX{} with considerable help from
\package{lhs2TeX}\footnote{\url{http://www.andres-loeh.de/lhs2tex/}} and
\package{ott}~\cite{ott}. The \package{lhs2TeX} software allows Haskell
code to be rendered more stylistically than a simple @verbatim@ environment
would allow. The table below maps Haskell source to glyphs appearing in this
dissertation:

\begin{table}[h]
\begin{center}
\begin{tabular}{c||c||l}
\textbf{Haskell} & \textbf{Typeset} & \textbf{Description} \\ \hline
@->@ & |->| & function arrow and other arrows\\
@=>@ & |=>| & constraint arrow\\
@*@ & |*| & the kind of types\\
@forall@ & |forall| & dependent irrelevant quantifier\\
@pi@ & |pi| & dependent relevant quantifier\\
@++@ & |++| & list concatenation\\
@:~~:@ & |:~~:| & heterogeneous propositional equality\\
@:~>@ & |:~>| & lambda-calculus arrow (from \pref{sec:stlc})\\
@undefined@ & |undefined| & canonical looping term
\end{tabular}
\end{center}
\caption{Typesetting of Haskell constructs}
\end{table}

In addition to the special formatting above, I assume a liberal overloading
of number literals, including in types. For example, I write |2| where I
really mean |Succ (Succ Zero)|, depending on the context.
