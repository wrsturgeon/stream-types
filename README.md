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

## Theorems

To locate the proof of a named theorem from Appendix B (e.g. "B.11"), search the source code in `theories/`.
Directly above each proof of a named theorem is a comment naming it: e.g., `(* Theorem B.11 *)`.

Currently, we have proven up to **B.33**, except those mentioned below.

## Issues

- Theorem B.19 (notation unclear)
- Theorems B.21-30 on prefix concatenation (clarify that the original `Inl` rule was a typo)
- Definition B.33 (not sure how to read it)
