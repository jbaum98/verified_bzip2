\NeedsTeXFormat{LaTeX2e}

\ProvidesClass{thesis}[2019/04/30 Thesis Class]

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax
\LoadClass{article}

\RequirePackage[fleqn]{amsmath}
\RequirePackage{amssymb}
\RequirePackage{mathtools}
\RequirePackage{hyperref}
\RequirePackage{cleveref}
\RequirePackage{parskip}

\RequirePackage{amsthm}

\RequirePackage{thmtools, thm-restate}

\RequirePackage[style=numeric-comp]{biblatex}
\bibliography{draft_paper}

\declaretheoremstyle[
  notefont=\mdseries\ttfamily, notebraces={(}{)},
  bodyfont=\normalfont,
]{lemma}

\declaretheorem[style=lemma,numberwithin=section]{theorem}
\declaretheorem[style=lemma,sibling=theorem]{proposition}
\declaretheorem[style=lemma,sibling=theorem]{lemma}
\declaretheorem[style=lemma,sibling=theorem]{corollary}

\declaretheorem[style=lemma,numberwithin=section]{definition}
\declaretheorem[style=lemma,numberwithin=section]{example}
\declaretheorem[style=lemma,numberwithin=section]{remark}

\RequirePackage[letterpaper,left=1.5in,right=1.5in,top=1in,bottom=1in]{geometry}

\setlength{\parskip}{1.5em}
\setlength{\parindent}{0in}

\RequirePackage{fontspec}
\setmonofont[
  Contextuals=Alternate,
  RawFeature=+XV00,
  Scale=0.9,
  UprightFont={*},
  ItalicFont={* Italic},
  BoldFont={* Semibold},
  BoldItalicFont={* Semibold Italic}
]{Iosevka}

\RequirePackage{listings}
\renewcommand{\lstlistingname}{Figure}

\begingroup
  \catcode0=12 %
  \makeatletter
  \g@addto@macro\lst@DefEC{%
    \lst@CCECUse\lst@ProcessLetter
    ∘% *** add Unicode characters ***
    ^^00% end marker
  }%
\endgroup


\RequirePackage{lstlangcoq}
\lstset{
  language=Coq,
  basicstyle=\ttfamily,
  mathescape=true,
  columns=fullflexible,
  belowskip=-0.5em plus 2pt,
  xleftmargin=0.25in,
  extendedchars=true,
  inputencoding=utf8,
}

\makeatletter
\newlength{\singlespace}
\newlength{\gobble}
\settowidth{\singlespace}{\lst@basicstyle \ }
\lst@Key{widthgobble}{0}{%
  \setlength{\gobble}{\lst@xleftmargin}
  \addtolength{\gobble}{-#1\singlespace}
  \def\lst@xleftmargin{\gobble}
}
\makeatother

\newcommand{\interlstingskip}{\nobreak\vskip 1em\goodbreak}

\newcommand{\var}[1]{\texttt{#1}}
\newcommand{\bvar}[1]{\texttt{\textbf{#1}}}

%% \newcommand{\compcent}[1]{\vcenter{\hbox{$#1\circ$}}}
%% \newcommand{\comp}{\mathbin{\mathchoice
%%   {\compcent\scriptstyle}{\compcent\scriptstyle}
%%   {\compcent\scriptscriptstyle}{\compcent\scriptscriptstyle}}}
\newcommand{\comp}{\circ}

\RequirePackage{proof}

\newcommand{\eqperm}{\overset{\mathtt{Perm}}{=\joinrel=\joinrel=}}
\newcommand{\eqstable}{\overset{\mathtt{Stable}}{=\joinrel=\joinrel=\joinrel=}}
\newcommand{\dplus}{\ensuremath{\mathbin{+\mkern-3mu+}}}
\newcommand{\lexle}{\ensuremath{\le_{\var{L}}}}
\newcommand{\equivle}{\ensuremath{\equiv_{\var{L}}}}

\RequirePackage{microtype}
\RequirePackage[sc]{mathpazo}
\linespread{1.05} % Palladio needs more leading (space between lines)
\RequirePackage[T1]{fontenc}

\RequirePackage[semibold]{sourcesanspro}
\RequirePackage{titlesec}
\titleformat*{\section}{\sffamily\Large\bfseries}
\titleformat*{\subsection}{\sffamily\Large}

\RequirePackage[margin=15pt,font=small,labelfont={bf,sf}]{caption}

\setcounter{tocdepth}{1}
\usepackage{xcolor}
\usepackage{colortbl}
\usepackage{paralist}
