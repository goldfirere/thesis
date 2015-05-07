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

%include intro.lhs
%include motivation.lhs
%include todays-haskell.lhs
\include{system-fc}
\include{dep-haskell}
\include{fcd}
\include{haskell-spec}
\include{type-inference}
\include{implementation}
\include{related}

\appendix

\include{fc}
\include{inference}

\newpage
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\nochapter{Bibliography}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\bibliographystyle{plainnat}
\bibliography{thesis}

\end{document}
