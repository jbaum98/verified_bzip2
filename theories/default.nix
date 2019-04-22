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
      sha256 = "0993lrnjlfhwn7lfyb0p1f87z5k8hkrxj4a12dkpmk3fgwnldk8v";
    })
  ];

  sourceRoot = ".";

  installPhase = ''
    mkdir -p $out/
    cp -R BWT/* $out/
  '';

  enableParallelBuilding = true;
}
