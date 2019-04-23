{ lib, stdenv, callPackage, texlive, makeFontsConf }:
{ srcDir, texFile, otherFiles ? [], tex ? texlive.scheme-basic, fonts ? [] }:
let outName = lib.removeSuffix ".tex" texFile; in
stdenv.mkDerivation rec {
  name = "${outName}.pdf";

  src = lib.sourceByRegex srcDir ([("^" + texFile + "$")] ++ otherFiles);

  buildInputs = [
    tex
  ];

  buildPhase = ''
    latexmk --xelatex ${texFile}
  '';

  installPhase = ''
    mkdir -p $out
    cp ${outName}.pdf $out/
  '';

  FONTCONFIG_FILE = makeFontsConf { fontDirectories = fonts; };
}
