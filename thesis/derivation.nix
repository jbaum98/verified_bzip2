{ lib, stdenv, callPackage, texlive, ghostscript, makeFontsConf, fira, iosevka, fira-mono, pythonPackages }:
let
  tex = texlive.combine ({
    inherit (texlive)
      # The Basics
      scheme-basic xetex euenc latexmk dvisvgm
      # Fonts
      collection-fontsrecommended fontspec
      collection-fontsextra
      # Bibliography
      biblatex biblatex-ieee biber
      # misc
      xstring parskip etoolbox logreq titlesec
      # Beamer
      beamer beamertheme-metropolis translator pgfopts pgfplots appendixnumberbeamer
      # org
      wrapfig ulem capt-of preprint mathtools
      minted fvextra fancyvrb upquote lineno ifplatform framed float
      thmtools
      epsf
      ;
  });

  fonts = [ fira iosevka fira-mono ];

in stdenv.mkDerivation rec {
  basename = "thesis";

  name = "${basename}.pdf";

  buildInputs = [
    tex
    ghostscript
    pythonPackages.pygments
  ];

  # FONTCONFIG_FILE = makeFontsConf { fontDirectories = fonts; };

  enableParallelBuilding = true;
}
