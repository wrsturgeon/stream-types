{ coq, coq-pkgs, ocaml, os-pkgs, ml-pkgs, src }:
let
  pname = "hammer";
  version = "none";
  propagatedBuildInputs = [ coq ocaml ml-pkgs.findlib ];
  mlPlugin = true;
  BINDIR = "bin";
  DESTDIR = "\${out}";
  ml-suffix =
    "/lib/ocaml/${ocaml.version}/site-lib"; # this is the magic incantation (<https://ryantm.github.io/nixpkgs/languages-frameworks/ocaml/#sec-language-ocaml-packaging>)
  coq-suffix =
    "/lib/coq/${coq.coq-version}/user-contrib"; # the other magic incantation, buried in the corresponding Coq page
  COQLIBINSTALL = "\${out}${coq-suffix}";
  COQDOCINSTALL = "\${out}/doc";
  COQPLUGININSTALL = "\${out}${ml-suffix}";
  COQTOPINSTALL = "\${out}/top";
  tactics = coq-pkgs.mkCoqDerivation {
    inherit propagatedBuildInputs mlPlugin src version BINDIR DESTDIR
      COQLIBINSTALL COQDOCINSTALL COQPLUGININSTALL COQTOPINSTALL;
    pname = "${pname}-tactics";
    buildPhase = "make tactics";
    installPhase = "make install-tactics";
  };
  plugin = coq-pkgs.mkCoqDerivation {
    inherit mlPlugin src version BINDIR DESTDIR COQLIBINSTALL COQDOCINSTALL
      COQPLUGININSTALL COQTOPINSTALL;
    pname = "${pname}-plugin";
    buildPhase = "make plugin";
    installPhase = "make install-plugin";
    propagatedBuildInputs = [ tactics ] ++ propagatedBuildInputs;
  };
in os-pkgs.stdenv.mkDerivation {
  inherit pname src version;
  phases = [ ];
  buildPhase = ":"; # just in case
  installPhase = ":"; # ^^
  propagatedBuildInputs = [ plugin tactics ];
}

