{ coq-pkgs, src }:
let
  pname = "libtactics";
  version = "none";
  coq-version = "${coq-pkgs.coq.coq-version}";
  flags =
    "-Q src LibTactics -w -implicit-core-hint-db"; # from <https://github.com/charguer/tlc/blob/master/src/_CoqProject>
  installdir = "$out/lib/coq/${coq-version}/user-contrib/LibTactics/";
in coq-pkgs.mkCoqDerivation {
  inherit pname src version;
  buildPhase = "coqc ${flags} src/LibTactics.v";
  installPhase = ''
    install -d ${installdir}
    install -m 0644 src/LibTactics.v    ${installdir}LibTactics.v
    install -m 0644 src/LibTactics.vo   ${installdir}LibTactics.vo
    install -m 0644 src/LibTactics.glob ${installdir}LibTactics.glob
  '';
}
