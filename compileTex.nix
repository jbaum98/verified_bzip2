{ lib, stdenv, callPackage, texlive, makeFontsConf }:
let
  filterByName = fileNames: builtins.filterSource (path: type:
    type == "regular" && lib.any (x: x == baseNameOf path) fileNames);
in
{ srcDir, texFile, otherFiles ? [], tex ? texlive.scheme-basic, fonts ? [] }:
let outName = lib.removeSuffix ".tex" texFile; in
stdenv.mkDerivation rec {
  name = "${outName}.pdf";

  src = filterByName ([ texFile ] ++ otherFiles) srcDir;

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
