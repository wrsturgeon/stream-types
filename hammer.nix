{ coq, coq-pkgs, ocaml, os-pkgs, ml-pkgs, src }:
let
  pname = "hammer";
  version = "none";
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
    pname = "${pname}-tactics";
    buildPhase = "make tactics";
    installPhase = "make install-tactics";
  };
  plugin = coq-pkgs.mkCoqDerivation {
    inherit mlPlugin src version COQLIBINSTALL COQDOCINSTALL COQPLUGININSTALL
      COQTOPINSTALL;
    pname = "${pname}-plugin";
    # buildPhase = "make DESTDIR=$out plugin";
    buildPhase = "make plugin";
    installPhase = "make DESTDIR=$out install-plugin";
    propagatedBuildInputs = [ tactics ] ++ propagatedBuildInputs;
  };
  tptp = import ./tptp.nix { inherit (os-pkgs) cmake stdenv z3; };
in os-pkgs.stdenv.mkDerivation {
  inherit pname src version;
  buildPhase = ":"; # just in case
  installPhase = ''
    mkdir -p $out/bin
    cp ${
      builtins.trace "${os-pkgs.z3-tptp}" os-pkgs.z3-tptp
    }/bin/z3-tptp $out/bin/z3_tptp
  '';
  propagatedBuildInputs = [ plugin tactics ]
    ++ (with os-pkgs; [ cvc4 eprover vampire z3 tptp ]);
}
