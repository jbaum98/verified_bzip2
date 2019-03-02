{ lib, stdenv, fetchFromGitHub, coq, fd }:
stdenv.mkDerivation {
  name = "verified_bzip2";

  nativeBuildInputs = [ coq fd ];

  preUnpack = ''
    mkdir theories
    cd theories
    cp ${./Makefile} Makefile
    cp ${./_CoqProject} _CoqProject
  '';

  srcs = [
    (lib.sourceFilesBySuffices ./BWT [ ".v" ])
    (fetchFromGitHub {
      name = "VST";
      owner = "PrincetonUniversity";
      repo = "VST";
      rev = lib.commitIdFromGitRepo ../.git/modules/VST;
      sha256 = "0yj2izsfmizmrgxwhr6nxqhfyb9asdpl0prss7djna38qjqpmyj0";
    })
  ];

  sourceRoot = ".";

  installPhase = ''
    mkdir -p $out/
    cp -R BWT/* $out/
  '';

  enableParallelBuilding = true;
}
