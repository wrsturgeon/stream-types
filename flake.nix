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
        pkgs = os-pkgs.coqPackages;
        hammer = import ./hammer.nix {
          inherit hammer-src nixpkgs system;
        }; # build it manually
      in {
        packages.default = pkgs.mkCoqDerivation {
          inherit pname version;
          src = ./.;
          buildInputs = [ hammer ];
        };
      });
}
