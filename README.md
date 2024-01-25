# Stream Types

## Authors

Theory developed mainly by Joseph Cutler under Dr. Benjamin Pierce at the University of Pennsylvania.

Proofs formalized mainly by Will Sturgeon and Cutler.

## Dependencies

### Nix (recommended, and also very cool)
Install Nix (in one line) [here](https://nixos.org/download#nix-install-macos).
After you're done, open this folder in a terminal and run these lines one by one:
```
nix profile install nixpkgs#direnv nixpkgs#nix-direnv
direnv allow
```
_Et voilà_. Now every time you navigate into this folder, you have all this project's dependencies, as if by magic.

### Manual

Install Coq ([here](https://coq.inria.fr/download)) and CoqHammer ([here](https://coqhammer.github.io/#installation)).

## Building

Open a terminal in this folder and run `make`.
