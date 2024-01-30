{ os-pkgs, coq-pkgs, src }:
let
  pname = "hammer";
  version = "none";
  coq = coq-pkgs.coq;
  ml-pkgs = coq.ocamlPackages;
  ocaml = ml-pkgs.ocaml;
  propagatedBuildInputs = [ coq ocaml ml-pkgs.findlib ];
  mlPlugin = true;
  ml-suffix =
    "/lib/ocaml/${ocaml.version}/site-lib"; # this is the magic incantation (<https://ryantm.github.io/nixpkgs/languages-frameworks/ocaml/#sec-language-ocaml-packaging>)
  coq-suffix =
    "/lib/coq/${coq.coq-version}/user-contrib"; # the other magic incantation, buried in the corresponding Coq page
  COQLIBINSTALL = "\${out}${coq-suffix}";
  COQDOCINSTALL = "\${out}/doc";
  COQPLUGININSTALL = "\${out}${ml-suffix}";
  COQTOPINSTALL = "\${out}/top";
  DESTDIR = "\${out}/";
  BINDIR = "bin/";
  tactics = coq-pkgs.mkCoqDerivation {
    inherit propagatedBuildInputs mlPlugin src version COQLIBINSTALL
      COQDOCINSTALL COQPLUGININSTALL COQTOPINSTALL DESTDIR BINDIR;
    pname = "${pname}";
    buildPhase = "make tactics";
    installPhase = "make install-tactics";
  };
  tptp = import ./tptp.nix { inherit (os-pkgs) cmake stdenv z3; };
  whole-enchilada = coq-pkgs.mkCoqDerivation {
    inherit mlPlugin pname src version COQLIBINSTALL COQDOCINSTALL
      COQPLUGININSTALL COQTOPINSTALL DESTDIR BINDIR;
    buildPhase = "make plugin";
    installPhase = ''
      mkdir -p ${DESTDIR}${BINDIR}
      make install-plugin
      make install-extra
    '';
    propagatedBuildInputs = [ tactics tptp ] ++ propagatedBuildInputs
      ++ (with os-pkgs; [ cvc4 eprover vampire z3 ]);
  };
in { inherit tactics whole-enchilada; }
