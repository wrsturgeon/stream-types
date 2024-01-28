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
  tactics = coq-pkgs.mkCoqDerivation {
    inherit propagatedBuildInputs mlPlugin src version COQLIBINSTALL
      COQDOCINSTALL COQPLUGININSTALL COQTOPINSTALL;
    pname = "${pname}";
    buildPhase = "make tactics";
    installPhase = "make install-tactics";
  };
  whole-enchilada = coq-pkgs.mkCoqDerivation {
    inherit mlPlugin pname src version COQLIBINSTALL COQDOCINSTALL
      COQPLUGININSTALL COQTOPINSTALL;
    buildPhase = "make plugin";
    installPhase = "make DESTDIR=$out install-plugin";
    propagatedBuildInputs = [ tactics ] ++ propagatedBuildInputs
      ++ (with os-pkgs; [ cvc4 eprover vampire z3 ]);
  };
in { inherit tactics whole-enchilada; }
