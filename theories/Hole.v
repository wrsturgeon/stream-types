From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LibTactics Require Import LibTactics.
From LambdaST Require Import
  Context
  FV
  Sets.

Inductive hole : Set :=
  | HoleHere
  | HoleCommaL (lhs : hole) (rhs : context)
  | HoleCommaR (lhs : context) (rhs : hole)
  | HoleSemicL (lhs : hole) (rhs : context)
  | HoleSemicR (lhs : context) (rhs : hole)
  .
Hint Constructors hole : core.
Derive Show for hole.
Derive Arbitrary for hole.

Fixpoint fill h y :=
  match h with
  | HoleHere => y
  | HoleCommaL lhs rhs => CtxComma (fill lhs y) rhs
  | HoleCommaR lhs rhs => CtxComma lhs (fill rhs y)
  | HoleSemicL lhs rhs => CtxSemic (fill lhs y) rhs
  | HoleSemicR lhs rhs => CtxSemic lhs (fill rhs y)
  end.

Inductive Fill : hole -> context -> context -> Prop :=
  | FillHere : forall y,
      Fill HoleHere y y
  | FillCommaL : forall y lhs rhs lhs',
      Fill lhs y lhs' ->
      Fill (HoleCommaL lhs rhs) y (CtxComma lhs' rhs)
  | FillCommaR : forall y lhs rhs rhs',
      Fill rhs y rhs' ->
      Fill (HoleCommaR lhs rhs) y (CtxComma lhs rhs')
  | FillSemicL : forall y lhs rhs lhs',
      Fill lhs y lhs' ->
      Fill (HoleSemicL lhs rhs) y (CtxSemic lhs' rhs)
  | FillSemicR : forall y lhs rhs rhs',
      Fill rhs y rhs' ->
      Fill (HoleSemicR lhs rhs) y (CtxSemic lhs rhs')
  .
Hint Constructors Fill : core.
(* Notation "G '(' D ')' 'is' GD" := (Fill G D GD) (at level 97, no associativity). *) (* Coq prints this oddly; better off without *)

Theorem reflect_fill : forall h y c,
  c = fill h y <-> Fill h y c.
Proof.
  split; intros.
  - subst. gen y. induction h; intros; cbn in *; constructor; apply IHh.
  - induction H; cbn; try rewrite IHFill; reflexivity.
Qed.
Hint Resolve reflect_fill : core.

Fixpoint fv_hole h :=
  match h with
  | HoleHere =>
      empty_set
  | HoleCommaL h c
  | HoleCommaR c h
  | HoleSemicL h c
  | HoleSemicR c h =>
      set_union (fv c) (fv_hole h)
  end.

(* Sanity check: *)
Theorem fv_hole_plug : forall h,
  SetEq (fv_hole h) (fv (fill h CtxEmpty)).
Proof. induction h; intros; split; sfirstorder. Qed.

Instance fv_hole_inst : FV hole := { fv := fv_hole }.

Lemma fv_fill : forall h plug ctx,
  Fill h plug ctx ->
  SetEq (fv ctx) (set_union (fv plug) (fv h)).
Proof. intros. induction H; sfirstorder. Qed.
Hint Resolve fv_fill : core.
