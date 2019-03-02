{ compileTex, texlive, fira, iosevka, fira-mono }:
let
  tex = texlive.combine ({
    inherit (texlive)
      # The Basics
      scheme-basic xetex euenc latexmk
      # Fonts
      collection-fontsrecommended fontspec
      # Bibliography
      biblatex biblatex-ieee biber
      # misc
      xstring parskip etoolbox logreq titlesec
      # Beamer
      beamer beamertheme-metropolis translator pgfopts pgfplots ulem appendixnumberbeamer
      ;
  });

  fonts = [ fira iosevka fira-mono ];

in compileTex {
  srcDir = ./.;
  texFile = "midpoint_presentation.tex";
  inherit tex fonts;
}
