\NeedsTeXFormat{LaTeX2e}

\ProvidesClass{thesis}[2019/04/30 Thesis Class]

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{article}}
\ProcessOptions\relax
\LoadClass{article}

\RequirePackage{amsmath}
\RequirePackage{amssymb}
\RequirePackage{mathtools}
\RequirePackage{hyperref}
\RequirePackage{cleveref}
\RequirePackage{parskip}

\RequirePackage{amsthm}
\makeatletter
\def\@endtheorem{\endtrivlist}
\makeatother

\RequirePackage{thmtools, thm-restate}

\RequirePackage[style=ieee]{biblatex}
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

\setlength{\parskip}{0in}
\setlength{\parindent}{0.25in}

\RequirePackage[letterpaper,margin=1in]{geometry}

\RequirePackage{fontspec}
\setmonofont[
  Contextuals=Alternate,
  RawFeature=+XV00,
  Scale=0.9,
  UprightFont={* Light},
  ItalicFont={* Light Italic},
  BoldFont={* Medium},
  BoldItalicFont={* Medium Italic}
]{Iosevka}

\RequirePackage{listings}
\RequirePackage{lstlangcoq}
\renewcommand{\lstlistingname}{Figure}
\lstset{
  language=Coq,
  basicstyle=\ttfamily,
  mathescape=true,
  columns=fullflexible,
}

\makeatletter
\newlength{\singlespace}
\settowidth{\singlespace}{\lst@basicstyle \ }
\lst@Key{widthgobble}{0}{%
  \def\lst@xleftmargin{-#1\singlespace}
}
\makeatother

\newcommand{\interlstingskip}{\nobreak\vskip 1em\goodbreak}
