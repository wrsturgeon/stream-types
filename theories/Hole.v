From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Context
  FV
  Sets.

Inductive hole : Set :=
  | HoleHere
  | HoleCommaL (h : hole) (g : context)
  | HoleCommaR (g : context) (h : hole)
  | HoleSemicL (h : hole) (g : context)
  | HoleSemicR (g : context) (h : hole)
  .
Hint Constructors hole : core.
Derive Show for hole.
Derive Arbitrary for hole.

Fixpoint fill h D :=
  match h with
  | HoleHere => D
  | HoleCommaL lhs rhs => CtxComma (fill lhs D) rhs
  | HoleCommaR lhs rhs => CtxComma lhs (fill rhs D)
  | HoleSemicL lhs rhs => CtxSemic (fill lhs D) rhs
  | HoleSemicR lhs rhs => CtxSemic lhs (fill rhs D)
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
  - subst. generalize dependent y. induction h; intros; cbn in *; constructor; apply IHh.
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

Lemma fv_fill_fn : forall h plug,
  SetEq (fv_ctx (fill h plug)) (set_union (fv plug) (fv h)).
Proof. intros. remember (fill h plug) as ctx eqn:E. apply reflect_fill in E. apply fv_fill. assumption. Qed.
Hint Resolve fv_fill_fn : core.

Inductive WFHole : hole -> Prop :=
  | WFHoleHere :
      WFHole HoleHere
  | WFHoleCommaL : forall h g,
      WFHole h ->
      WFContext g ->
      DisjointSets (fv h) (fv g) ->
      WFHole (HoleCommaL h g)
  | WFHoleCommaR : forall h g,
      WFHole h ->
      WFContext g ->
      DisjointSets (fv h) (fv g) ->
      WFHole (HoleCommaR g h)
  | WFHoleSemicL : forall h g,
      WFHole h ->
      WFContext g ->
      DisjointSets (fv h) (fv g) ->
      WFHole (HoleSemicL h g)
  | WFHoleSemicR : forall h g,
      WFHole h ->
      WFContext g ->
      DisjointSets (fv h) (fv g) ->
      WFHole (HoleSemicR g h)
  .
Hint Constructors WFHole : core.

Theorem wf_fill_reflect : forall h d g,
  FillWith d h g -> (
    WFContext g <-> (
      WFHole h /\
      WFContext d /\
      DisjointSets (fv h) (fv d))).
Proof.
  intros h d g H. induction H; cbn in *; intros; [sfirstorder | | | |];
  split; intros; sinvert H0; apply fv_fill in H; sauto.
Qed.
Hint Resolve wf_fill_reflect : core.

Theorem wf_fill : forall h d,
  WFContext (fill h d) <-> (WFHole h /\ WFContext d /\ DisjointSets (fv h) (fv d)).
Proof.
  intros h d.
  remember (fill h d) as g.
  apply reflect_fill in Heqg.
  hauto l: on use: wf_fill_reflect.
Qed.
Hint Resolve wf_fill : core.

Theorem hmm : forall G x y z s t r ctr,
  (ctr = CtxComma \/ ctr = CtxSemic) ->
  ~fv G z ->
  SetEq
    (set_union
       (set_minus (fv (fill G (CtxHasTy z r))) (singleton_set z))
       (set_union (singleton_set x) (singleton_set y)))
    (fv (fill G (ctr (CtxHasTy x s) (CtxHasTy y t)))).
Proof.
  cbn. intros. remember (fill G (CtxHasTy z r)) as Gz eqn:Ehz.
  remember (fill G (ctr (CtxHasTy x s) (CtxHasTy y t))) as Gxy eqn:Ehxy.
  apply reflect_fill in Ehz. apply reflect_fill in Ehxy.
  apply fv_fill in Ehz. apply fv_fill in Ehxy.
  hauto q: on.
Qed.

Theorem hmm' : forall G x y z s t r ctr,
  (ctr = CtxComma \/ ctr = CtxSemic) ->
  ~(fv G x) ->
  ~(fv G y) ->
  x <> y ->
  WFContext (fill G (CtxHasTy z r)) ->
  WFContext
    (fill G (ctr (CtxHasTy x s) (CtxHasTy y t))).
Proof.
  intros G x y z s t r ctr Hctr Hx Hy Hxy H. apply wf_fill in H as [H1 [H2 H3]]. sinvert H2. apply wf_fill.
  repeat split; intros; [eassumption | sauto | |]; destruct Hctr; sfirstorder.
Qed.
