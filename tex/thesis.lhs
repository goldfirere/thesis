%% -*- mode: LaTeX -*-

\newif \ifdraft \drafttrue
\newif \ifproposal \proposaltrue
\documentclass[12pt,oneside]{book}

%include rae.fmt

\newcommand{\Title}{DEPENDENT TYPES IN HASKELL: THEORY AND PRACTICE}
\newcommand{\Author}{Richard A.~Eisenberg}
\newcommand{\Advisor}{Stephanie Weirich}
\newcommand{\Year}{2016}

\input{preamble}

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

%include 1-intro.lhs
%include 2-motivation.lhs
%include 3-todays-haskell.lhs
\include{4-system-fc}
\include{5-dep-haskell}
\include{6-fcd}
\include{7-haskell-spec}
\include{8-type-inference}
\include{9-implementation}
\include{10-related}

\appendix

\include{a-fc}
\include{b-inference}

\newpage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\nochapter{Bibliography}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\bibliographystyle{plainnat}
\bibliography{thesis}

\end{document}
