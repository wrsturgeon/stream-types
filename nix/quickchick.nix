{ coq-pkgs, src }:
let
  pname = "quickchick";
  version = "none";
  coq = coq-pkgs.coq;
  ml-pkgs = coq.ocamlPackages;
  ocaml = ml-pkgs.ocaml;
  mlPlugin = true;
  ml-suffix =
    "/lib/ocaml/${ocaml.version}/site-lib"; # this is the magic incantation (<https://ryantm.github.io/nixpkgs/languages-frameworks/ocaml/#sec-language-ocaml-packaging>)
  coq-suffix =
    "/lib/coq/${coq.coq-version}/user-contrib"; # the other magic incantation, buried in the corresponding Coq page
  COQLIBINSTALL = "\${out}${coq-suffix}";
  COQDOCINSTALL = "\${out}/doc";
  COQPLUGININSTALL = "\${out}${ml-suffix}";
  COQTOPINSTALL = "\${out}/top";
in coq-pkgs.mkCoqDerivation {
  inherit mlPlugin pname src version COQLIBINSTALL COQDOCINSTALL
    COQPLUGININSTALL COQTOPINSTALL;
  INSTALLDIR = COQPLUGININSTALL;
  propagatedBuildInputs = [ coq ocaml ]
    ++ (with coq-pkgs; [ mathcomp-ssreflect simple-io ])
    ++ (with ml-pkgs; [ cppo findlib ocamlbuild ]);
}
