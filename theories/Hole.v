From LambdaST Require Import
  Context
  FV
  Ident.
From Hammer Require Import
  Tactics.

Inductive hole : Set :=
  | HoleHere
  | HoleCommaL (h : hole) (g : context)
  | HoleCommaR (g : context) (h : hole)
  | HoleSemicL (h : hole) (g : context)
  | HoleSemicR (g : context) (h : hole)
  .

Fixpoint fill h D :=
  match h with
  | HoleHere => D
  | HoleCommaL lhs rhs => CtxComma (fill lhs D) rhs
  | HoleCommaR lhs rhs => CtxComma lhs (fill rhs D)
  | HoleSemicL lhs rhs => CtxSemic (fill lhs D) rhs
  | HoleSemicR lhs rhs => CtxSemic lhs (fill rhs D)
  end.

Inductive FillWith d : hole -> context -> Prop :=
  | FillHere :
      FillWith d HoleHere d
  | FillCommaL : forall h g' g,
      FillWith d h g ->
      FillWith d (HoleCommaL h g') (CtxComma g g')
  | FillCommaR : forall g h g',
      FillWith d h g' ->
      FillWith d (HoleCommaR g h) (CtxComma g g')
  | FillSemicL : forall h g' g,
      FillWith d h g ->
      FillWith d (HoleSemicL h g') (CtxSemic g g')
  | FillSemicR : forall g h g',
      FillWith d h g' ->
      FillWith d (HoleSemicR g h) (CtxSemic g g')
  .

Theorem reflect_fill : forall h d g,
  g = fill h d <-> FillWith d h g.
Proof.
  split; intros.
  - subst. generalize dependent d. induction h; intros; simpl in *; constructor; apply IHh.
  - induction H; simpl; try rewrite IHFillWith; reflexivity.
Qed.

Fixpoint fv_hole (h : hole) : set ident :=
  match h with
  | HoleHere => empty_set
  | HoleCommaL h g
  | HoleCommaR g h
  | HoleSemicL h g
  | HoleSemicR g h => set_union (fv_hole h) (fv g)
  end.

Instance fv_hole_inst : FV hole := { fv := fv_hole }.

Theorem fv_fill_reflect: forall H D G,
  FillWith H D G ->
  forall x, fv G x <-> fv H x \/ fv D x.
Proof. intros H D G Hfill. induction Hfill; sfirstorder. Qed.

Theorem fv_fill : forall H D,
  forall x, fv (fill H D) x <-> fv H x \/ fv D x.
Proof.
  intros H D.
  remember (fill H D).
  hauto lq: on use:fv_fill_reflect, reflect_fill.
Qed.

Inductive wf_hole : hole -> Prop :=
| wf_HoleHere : wf_hole HoleHere
| wf_HoleCommaL : forall h g,
  wf_hole h ->
  WFContext g ->
  Disjoint (fv h) (fv g) ->
  wf_hole (HoleCommaL h g)
| wf_HoleCommaR : forall h g,
  wf_hole h ->
  WFContext g ->
  Disjoint (fv h) (fv g) ->
  wf_hole (HoleCommaR g h)
| wf_HoleSemicL : forall h g,
  wf_hole h ->
  WFContext g ->
  Disjoint (fv h) (fv g) ->
  wf_hole (HoleSemicL h g)
| wf_HoleSemicR : forall h g,
  wf_hole h ->
  WFContext g ->
  Disjoint (fv h) (fv g) ->
  wf_hole (HoleSemicR g h)
.

Theorem wf_fill_reflect : forall h d g,
  FillWith d h g ->
  WFContext g <-> wf_hole h /\ WFContext d /\ Disjoint (fv h) (fv d).
Proof.
  intros h d g H. induction H; cbn in *; intros; [sfirstorder | | | |];
  (split; [sauto lq: on use:fv_fill_reflect | sauto l: on use:fv_fill_reflect]).
Qed.

Theorem wf_fill : forall h d,
  WFContext (fill h d) <-> (wf_hole h /\ WFContext d /\ Disjoint (fv h) (fv d)).
Proof.
  intros h d.
  remember (fill h d) as g.
  apply reflect_fill in Heqg.
  hauto l: on use: wf_fill_reflect.
Qed.
