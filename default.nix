{
pkgs ? import (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/bc9df0f66110039e495b6debe3a6cda4a1bb0fed.tar.gz";
  sha256 = "0y2w259j0vqiwjhjvlbsaqnp1nl2zwz6sbwwhkrqn7k7fmhmxnq1";
}) {}

}:

#let coq = import (fetchTarball https://github.com/coq/coq-on-cachix/tarball/master) {}; in

let coq = import (fetchTarball {
    url = https://github.com/vbgl/coq/archive/ltac2+noinit.tar.gz;
    sha256 = "0bcl5mra9xb4y9xkmlrdfm3k3if753dpdnj29ynb24bk8cagi1dz";
  }
) {};
in

let callPackage = pkgs.newScope { inherit coq; }; in

rec {
  stdlib2 = callPackage ./stdlib2.nix { };

  math-comp = callPackage ./math-comp.nix { inherit stdlib2; };
}
