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
      beamer beamertheme-metropolis translator pgfopts pgfplots
      ulem appendixnumberbeamer
      lkproof
      ;
  });

  fonts = [ fira iosevka fira-mono ];

in compileTex {
  srcDir = ./.;
  texFile = "final_presentation.tex";
  otherFiles = [ "img.*" ];
  inherit tex fonts;
}
