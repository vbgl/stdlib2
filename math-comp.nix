{ stdenv, coq, stdlib2 }:

stdenv.mkDerivation {
  name = "math-comp";
  src = ./math-comp/mathcomp;

  buildInputs = [ coq stdlib2 ];

  buildFlags = "ssreflect/div.vo ssreflect/fingraph.vo";

  installFlags = [
    "-f Makefile.coq"
    "COQLIB=$(out)/lib/coq/${coq.coq-version}"
  ];

  installPhase = "mkdir -p $out";
}
