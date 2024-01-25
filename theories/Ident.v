From Coq Require Import
  Strings.String
  Classes.EquivDec
  Logic.Decidable.

Definition ident : Set := string.

From Hammer Require Import Tactics.

Bind Scope string_scope with ident.

Definition eq_id : ident -> ident -> bool := eqb.
Notation "a '=i' b" := (eq_id a b) (at level 98).

Theorem eq_id_refl : forall x, (x =i x) = true.
Proof.
hauto lq: on use:eqb_refl.
Qed.

Theorem eq_id_notrefl : forall x y, x <> y -> (x =i y) = false.
Proof.
sfirstorder use:eqb_neq.
Qed.


Instance EqDec : EqDec Ident.ident eq :=
{
  equiv_dec x y := string_dec x y
}.