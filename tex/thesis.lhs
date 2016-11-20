%% -*- mode: LaTeX -*-

\documentclass[12pt,oneside,draft]{book}

%include rae.fmt

\input{texpreamble}
\input{thesispreamble}

\title{\Title}
\author{\Author}

\begin{document}

\hypersetup{pageanchor=false}
\pagenumbering{roman}
\pagestyle{fancy}
\frenchspacing
\numberwithin{equation}{section}

\newcommand{\doublespaced}{\renewcommand{\baselinestretch}{2}\normalfont}
\newcommand{\singlespaced}{\renewcommand{\baselinestretch}{1}\normalfont}

\include{titlepage}
\include{copyright}
\include{dedication}
\include{acks}
\include{abstract}

\singlespaced

\tableofcontents

\newpage

% \listoftables

\listoffigures

\newpage
\setcounter{page}{1}
\pagenumbering{arabic}
\hypersetup{pageanchor=true}
% \pagestyle{headings}

%include intro.lhs
%include prelim.lhs
%include motivation.lhs
%include dep-haskell.lhs
%include pico.lhs
%include type-inference.lhs
%include implementation.lhs
%include related.lhs
%

\appendix
\tolerance 9999
\emergencystretch 3em

\setlist[enumerate]{itemsep=0pt}
\setlist[itemize]{itemsep=0pt}
\setlist[description]{itemsep=0pt}

%include typo.lhs
\include{app-rules}
\include{app-pico}
\include{app-inference-rules}
\include{app-inference}
\include{app-eqtype}

\newpage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\nochapter{Bibliography}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\bibliographystyle{plainnat}
\bibliography{../bib/rae}

\end{document}

%%  LocalWords:  pageanchor lhs prelim dep
