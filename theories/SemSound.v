From LambdaST Require Import
    Terms
    Semantics
    Typing
    Prefix
    Environment.
Require Import Coq.Program.Equality.

From Hammer Require Import Tactics.


Theorem soundout : forall G e e' s eta p,
    Typed G e s ->
    EnvTyped eta G ->
    Step eta e e' p ->
    PfxTyped p s
.
Proof.
Admitted.