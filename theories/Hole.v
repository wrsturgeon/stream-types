From LambdaST Require Import
  Context.

Inductive hole : Set :=
  | HoleHere
  | HoleCommaL (lhs : hole) (rhs : context)
  | HoleCommaR (lhs : context) (rhs : hole)
  | HoleSemicL (lhs : hole) (rhs : context)
  | HoleSemicR (lhs : context) (rhs : hole)
  .
Hint Constructors hole : core.

Fixpoint fill h y :=
  match h with
  | HoleHere => y
  | HoleCommaL lhs rhs => CtxComma (fill lhs y) rhs
  | HoleCommaR lhs rhs => CtxComma lhs (fill rhs y)
  | HoleSemicL lhs rhs => CtxSemic (fill lhs y) rhs
  | HoleSemicR lhs rhs => CtxSemic lhs (fill rhs y)
  end.

Inductive FillWith y : hole -> context -> Prop :=
  | FillHere :
      FillWith y HoleHere y
  | FillCommaL : forall lhs rhs lhs',
      FillWith y lhs lhs' ->
      FillWith y (HoleCommaL lhs rhs) (CtxComma lhs' rhs)
  | FillCommaR : forall lhs rhs rhs',
      FillWith y rhs rhs' ->
      FillWith y (HoleCommaR lhs rhs) (CtxComma lhs rhs')
  | FillSemicL : forall lhs rhs lhs',
      FillWith y lhs lhs' ->
      FillWith y (HoleSemicL lhs rhs) (CtxSemic lhs' rhs)
  | FillSemicR : forall lhs rhs rhs',
      FillWith y rhs rhs' ->
      FillWith y (HoleSemicR lhs rhs) (CtxSemic lhs rhs')
  .
Hint Constructors FillWith : core.

Theorem reflect_fill : forall h y c,
  c = fill h y <-> FillWith y h c.
Proof.
  split; intros.
  - subst. generalize dependent y. induction h; intros; cbn in *; constructor; apply IHh.
  - induction H; cbn; try rewrite IHFillWith; reflexivity.
Qed.
Hint Resolve reflect_fill : core.
