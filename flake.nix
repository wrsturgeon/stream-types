{
  description = "Operational semantics of general programs with streams.";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    hammer-src = {
      url = "github:lukaszcz/coqhammer";
      flake = false;
    };
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };
  outputs = { flake-utils, hammer-src, nixpkgs, self }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pname = "lambda-st";
        version = "0.0.1";
        os-pkgs = import nixpkgs { inherit system; };
        coq-pkgs = os-pkgs.coqPackages;
        hammer = let
          coq = coq-pkgs.coq;
          ml-pkgs = coq.ocamlPackages; # guaranteed Coq-OCaml version match
          ocaml = ml-pkgs.ocaml;
        in import ./hammer.nix {
          inherit coq coq-pkgs ml-pkgs ocaml os-pkgs;
          src = hammer-src;
        };
      in {
        packages.default = coq-pkgs.mkCoqDerivation {
          inherit pname version;
          src = ./.;
          buildInputs = [ hammer ];
        };
      });
}
