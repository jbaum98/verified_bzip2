\NeedsTeXFormat{LaTeX2e}

\ProvidesClass{thesis}[2019/04/30 Thesis Class]

\DeclareOption*{\PassOptionsToClass{\CurrentOption}{acmart}}
\ProcessOptions\relax
\LoadClass{acmart}

\settopmatter{printfolios=true,printccs=false,printacmref=false}

\RequirePackage{mathtools}
\RequirePackage{hyperref}
\RequirePackage[capitalise]{cleveref}
\RequirePackage{parskip}
\RequirePackage{listings}
\RequirePackage{lstlangcoq}
\RequirePackage{thmtools, thm-restate}
\RequirePackage{xcolor}
\RequirePackage{colortbl}
\RequirePackage{proof}
\RequirePackage{fontspec}

\setmonofont[
  Contextuals=Alternate,
  RawFeature=+XV00,
  Scale=0.9,
  UprightFont={*},
  ItalicFont={* Italic},
  BoldFont={* Heavy},
  BoldItalicFont={* Heavy Italic}
]{Iosevka}

\newfontfamily\notofamily{Noto Serif}

\lstset{
  language=Coq,
  basicstyle=\ttfamily,
  mathescape=true,
  columns=flexible,
  keepspaces=true,
  extendedchars=true,
  inputencoding=utf8,
  belowskip=0pt,
}

\newcommand{\var}[1]{\texttt{\textup{#1}}}
\newcommand{\bvar}[1]{\texttt{\textbf{#1}}}
\newcommand{\comp}{\circ}

\newcommand{\eqperm}{\overset{\text{\texttt{Perm}}}{=\joinrel=\joinrel=}}
\newcommand{\eqstable}{\overset{\text{\texttt{Stable}}}{=\joinrel=\joinrel=\joinrel=}}
\newcommand{\dplus}{\ensuremath{\mathbin{+\mkern-3mu+}}}
\newcommand{\lexle}{\ensuremath{\le_{\var{L}}}}
\newcommand{\equivle}{\ensuremath{\equiv_{\var{L}}}}
