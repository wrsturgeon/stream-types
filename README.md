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

## Style?

Very not set in stone. My mind could easily be changed on any of these. At the moment, though, just for my own memory:
- Anything that's a `Prop` or usually ends up fully saturated as a `Prop`: uppercase.
- Constructors for inductive/variant types: uppercase.
- Everything else: lowercase.
- Two-space indentation.
- Inductive/variant types have all their constructors (e.g. `| Nil`) on separate lines, each indented.
    - Also, unless everything fits on one line, `forall`s go on the same line as the constructor, and everything else goes after, indented again.
