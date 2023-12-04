{
  description = "Operational semantics of general programs with streams.";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
  };
  outputs = { flake-utils, nixpkgs, self }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        name = "lambda-st";
        version = "0.0.1";
        system-nixpkgs = import nixpkgs { inherit system; };
        coq-pkgs = system-nixpkgs.coqPackages;
      in {
        packages.default = system-nixpkgs.stdenv.mkDerivation {
          inherit name version;
          src = ./.;

          buildInputs = (with system-nixpkgs; [ git ])
            ++ (with coq-pkgs; [ coq ]);
          buildPhase = ''
            make
          '';
        };
      });
}
