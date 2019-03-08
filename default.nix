{
  pkgs ? import <nixpkgs> {}
}:

let coq = import (fetchTarball https://github.com/coq/coq-on-cachix/tarball/master) {}; in

let callPackage = pkgs.newScope { inherit coq; }; in

rec {
  stdlib2 = callPackage ./stdlib2.nix { };

  math-comp = callPackage ./math-comp.nix { inherit stdlib2; };
}
