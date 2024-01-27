From Coq Require Import
  Strings.String
  Classes.EquivDec
  Logic.Decidable.
From Hammer Require Import
  Tactics.

Definition ident : Set := string.
Hint Unfold ident : core.

Bind Scope string_scope with ident.

Definition eq_id : ident -> ident -> bool := eqb.
Notation "a '=i' b" := (eq_id a b) (at level 98).
Hint Unfold eq_id : core.

Theorem eq_id_refl : forall x, (x =i x) = true.
Proof. hauto lq: on use:eqb_refl. Qed.
Hint Resolve eq_id_refl : core.

Theorem eq_id_notrefl : forall x y, x <> y -> (x =i y) = false.
Proof. sfirstorder use:eqb_neq. Qed.
Hint Resolve eq_id_notrefl : core.

Instance EqDec : EqDec Ident.ident eq := { equiv_dec x y := string_dec x y }.
