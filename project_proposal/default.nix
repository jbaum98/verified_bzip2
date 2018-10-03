{ lib, stdenv, callPackage, texlive, ghostscript }:
let
  tex = texlive.combine ({
    inherit (texlive)
      # The Basics
      scheme-basic xetex euenc latexmk
      # Fonts
      collection-fontsrecommended
      # Bibliography
      biblatex bibtex biblatex-ieee
      # misc
      xstring parskip etoolbox logreq
      ;
  });

in stdenv.mkDerivation rec {
  basename = "written_project_proposal";

  name = "${basename}.pdf";

  buildInputs = [
    tex
    ghostscript
  ];

  phases = [ "unpackPhase" "buildPhase" "installPhase" ];

  unpackPhase =
  ''
    cp ${./. + "/${basename}.tex"} ${basename}.tex
    cp ${./. + "/${basename}.bib"} ${basename}.bib
  '';

  buildPhase = ''
    latexmk --xelatex ${basename}.tex -jobname=${basename}
  '';

  installPhase = ''
    cp ${basename}.pdf $out
  '';
}
