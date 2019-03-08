{ stdenv, coq, stdlib2 }:

stdenv.mkDerivation {
  name = "math-comp";
  src = ./math-comp/mathcomp;

  buildInputs = [ coq stdlib2 ];

  buildFlags = "ssreflect/eqtype.vo";

  installFlags = [
    "-f Makefile.coq"
    "COQLIB=$(out)/lib/coq/${coq.coq-version}"
  ];

  installPhase = "mkdir -p $out";
}
