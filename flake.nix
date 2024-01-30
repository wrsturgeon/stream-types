{
  description = "Operational semantics of general programs with streams.";
  inputs = {
    flake-utils.url = "github:numtide/flake-utils";
    hammer-src = {
      url = "github:lukaszcz/coqhammer";
      flake = false;
    };
    libtactics-src = {
      url = "github:charguer/tlc";
      flake = false;
    };
    nixpkgs.url = "github:nixos/nixpkgs/nixos-unstable";
    qc-src = {
      url = "github:quickchick/quickchick";
      flake = false;
    };
  };
  outputs = { flake-utils, hammer-src, libtactics-src, nixpkgs, qc-src, self }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pname = "lambda-st";
        version = "0.0.1";
        os-pkgs = import nixpkgs { inherit system; };
        coq-pkgs = os-pkgs.coqPackages;
        hammer = (import nix/hammer.nix {
          inherit coq-pkgs os-pkgs;
          src = hammer-src;
        }).tactics;
        libtactics = import nix/libtactics.nix {
          inherit coq-pkgs;
          src = libtactics-src;
        };
        quickchick = import nix/quickchick.nix {
          inherit coq-pkgs;
          src = qc-src;
        };
      in {
        packages.default = coq-pkgs.mkCoqDerivation {
          inherit pname version;
          src = ./.;
          buildInputs = builtins.trace "${libtactics}"
            (builtins.trace "${quickchick}" [ hammer libtactics quickchick ]);
        };
      });
}
