From Coq Require Import String.
From LambdaST Require Import
  Environment
  Inert
  Sets.

(* Agree Inert means "including empty on agreement";
 * Agree Jumpy means "not including empty on agreement." *)
Definition Agree (i : inertness) (n n' : env) (s s' : set string) : Prop :=
  (MaximalOn s n -> MaximalOn s' n') /\
  (i = Inert -> EmptyOn s n -> EmptyOn s' n').
Arguments Agree/ i n n' s s'.
Hint Unfold Agree : core.
