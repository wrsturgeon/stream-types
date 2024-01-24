From Coq Require Import
  List
  String.

From Hammer Require Import Tactics.

Definition disjoint {A : Type} (xs : list A) (ys : list A) : Prop :=
  forall x, (In x xs -> ~In x ys) /\ (In x ys -> ~ In x xs).

Theorem disjoint_sym {A : Type} : forall (xs : list A) ys, disjoint xs ys -> disjoint ys xs.
Proof.
sfirstorder.
Qed.
  