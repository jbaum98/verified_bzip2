{ lib, stdenv, callPackage, texlive, ghostscript, makeFontsConf, fira, iosevka }:
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
      beamer beamertheme-metropolis translator pgfopts pgfplots ulem
      ;
  });

  fonts = [ fira iosevka ];

in stdenv.mkDerivation rec {
  basename = "midpoint_presentation";

  name = "${basename}.pdf";

  buildInputs = [
    tex
    ghostscript
  ];

  phases = [ "unpackPhase" "buildPhase" "installPhase" ];

  unpackPhase =
  ''
    cp ${./. + "/${basename}.tex"} ${basename}.tex
  '';

  buildPhase = ''
    latexmk --xelatex ${basename}.tex -jobname=${basename}
  '';

  installPhase = ''
    cp ${basename}.pdf $out
  '';

  FONTCONFIG_FILE = makeFontsConf { fontDirectories = fonts; };

  enableParallelBuilding = true;
}
