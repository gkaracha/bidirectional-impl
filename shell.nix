with (import <nixpkgs> {}).pkgs;
let
  prototype = pkgs.haskellPackages.callPackage ./. {};
in prototype.env
