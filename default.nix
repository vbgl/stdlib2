{
pkgs ? import (fetchTarball {
  url = "https://github.com/NixOS/nixpkgs/archive/31c38894c90429c9554eab1b416e59e3b6e054df.tar.gz";
  sha256 = "1fv14rj5zslzm14ak4lvwqix94gm18h28376h4hsmrqqpnfqwsdw";
}) {}

}:

#let coq = import (fetchTarball https://github.com/coq/coq-on-cachix/tarball/master) {}; in

let coq = import (fetchTarball {
    url = https://github.com/vbgl/coq/archive/ltac2+noinit.tar.gz;
    sha256 = "09dybarsj56d3sqi1hjjnqb5gik2491am6qzchcwjar2jy37crq3";
  }
) {};
in

let callPackage = pkgs.newScope { inherit coq; }; in

rec {
  stdlib2 = callPackage ./stdlib2.nix { };

  math-comp = callPackage ./math-comp.nix { inherit stdlib2; };
}
