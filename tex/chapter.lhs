%% -*- mode: LaTeX; compile-command: "cd ..; make compile" -*-

%% build just one chapter of thesis

\documentclass[12pt,oneside,draft]{book}

%include rae.fmt

\input{texpreamble}
\input{thesispreamble}

\begin{document}

%include thechapter.lhs

\newpage
\nochapter{Bibliography}

\bibliographystyle{plainnat}
\bibliography{../bib/rae}

\end{document}
