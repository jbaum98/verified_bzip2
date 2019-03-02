{ compileTex, texlive }:
let
  tex = texlive.combine ({
    inherit (texlive)
      # The Basics
      scheme-basic xetex euenc latexmk
      # Fonts
      collection-fontsrecommended
      # Bibliography
      biblatex biblatex-ieee biber
      # misc
      xstring parskip etoolbox logreq titlesec
      ;
  });
in compileTex {
  srcDir = ./.;
  texFile = "written_project_proposal.tex";
  otherFiles = [ "written_project_proposal.bib" ];
  inherit tex;
}
