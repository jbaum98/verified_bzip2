{ compileTex, texlive }:
let
  tex = texlive.combine ({
    inherit (texlive)
      # The Basics
      scheme-basic xetex euenc latexmk
      # Fonts
      collection-fontsrecommended fontspec
      # Bibliography
      biblatex biblatex-ieee biber
      etoolbox logreq xstring
      # thmtools
      thmtools epsf
      ;
    });
in compileTex {
  srcDir = ./.;
  texFile = "draft_paper.tex";
  otherFiles = [ "draft_paper.bib" ];
  inherit tex;
}
