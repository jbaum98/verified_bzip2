{ lib, pkgs }:
let
  compileTex = lib.callPackageWith pkgs ./compileTex.nix {};
  callPackage = lib.callPackageWith (pkgs // { inherit compileTex; });
in
{
  midpoint_presentation = callPackage ./midpoint_presentation {};
  final_presentation = callPackage ./final_presentation {};
  draft_paper = callPackage ./draft_paper {};
  written_project_proposal = callPackage ./written_project_proposal {};
}
