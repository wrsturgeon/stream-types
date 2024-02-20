From Hammer Require Import Tactics.

Variant inertness : Set := Inert | Jumpy.
Hint Constructors inertness : core.

Definition i_leq i1 i2 :=
  match i1, i2 with
  | Inert, i => True
  | Jumpy , Jumpy => True
  | Jumpy , Inert => False
  end.
Arguments i_leq i1 i2/.
Hint Unfold i_leq : i1 i2.

Definition i_ub i1 i2 i3 :=
  (i1 = Jumpy \/ i2 = Jumpy) -> i3 = Jumpy.
Arguments i_ub i1 i2 i3/.
Hint Unfold i_ub : i1 i2 i3.

Theorem i_ub_inert : forall i1 i2, i_ub i1 i2 Inert -> i1 = Inert /\ i2 = Inert.
Proof. sauto lq: on rew: off. Qed.

(* if i is required to be inert, then p must hold.*)
Definition inert_guard (p : Prop) (i : inertness) : Prop :=
  i = Inert -> p.
Arguments inert_guard p i/.
Hint Unfold inert_guard : core.

Theorem i_ub_is_ub : forall i1 i2 i3,
  i_ub i1 i2 i3 ->
  i_leq i1 i3 /\ i_leq i2 i3.
Proof.
  intros. destruct i1; destruct i2; destruct i3; sfirstorder.
Qed.
