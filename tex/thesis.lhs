%% -*- mode: LaTeX -*-

\documentclass[12pt,oneside]{book}

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
\ifproposal\else
\include{copyright}
\include{acks}
\include{abstract}
\fi

\singlespaced

\tableofcontents

\ifproposal\else
\newpage

\listoftables

\listoffigures
\fi

\newpage
\setcounter{page}{1}
\pagenumbering{arabic}
\hypersetup{pageanchor=true}

%include intro.lhs
%include prelim.lhs
%include motivation.lhs
%include dep-haskell.lhs
%include pico.lhs
%include haskell-spec.lhs
\include{type-inference}
\include{implementation}
\include{related}
%
\ifproposal
\include{proposal}
\fi

\appendix

\setlist[enumerate]{itemsep=0pt}
\setlist[itemize]{itemsep=0pt}
\setlist[description]{itemsep=0pt}

%include typo.lhs
\include{app-pico}
\include{inference}

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
