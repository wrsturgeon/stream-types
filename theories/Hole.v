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
  | WFHoleCommaL : forall lhs rhs,
      WFHole lhs ->
      WFContext rhs ->
      DisjointSets (fv lhs) (fv rhs) ->
      WFHole (HoleCommaL lhs rhs)
  | WFHoleCommaR : forall lhs rhs,
      WFContext lhs ->
      WFHole rhs ->
      DisjointSets (fv lhs) (fv rhs) ->
      WFHole (HoleCommaR lhs rhs)
  | WFHoleSemicL : forall lhs rhs,
      WFHole lhs ->
      WFContext rhs ->
      DisjointSets (fv lhs) (fv rhs) ->
      WFHole (HoleSemicL lhs rhs)
  | WFHoleSemicR : forall lhs rhs,
      WFContext lhs ->
      WFHole rhs ->
      DisjointSets (fv lhs) (fv rhs) ->
      WFHole (HoleSemicR lhs rhs)
  .
Hint Constructors WFHole : core.

Theorem fill_disjoint_l : forall G D GD (s : context),
  Fill G D GD ->
  DisjointSets (fv GD) (fv s) ->
  DisjointSets (fv G) (fv s).
Proof.
  cbn in *. intros G D GDG s Hf Hd. split; intros H C; specialize (Hd x) as [Hlr Hrl];
  (apply Hrl; [| eapply fv_fill; [| right]]; eassumption).
Qed.
Hint Resolve fill_disjoint_l : core.

Theorem fill_disjoint_r : forall G D GD (s : context),
  Fill G D GD ->
  DisjointSets (fv s) (fv GD) ->
  DisjointSets (fv s) (fv G).
Proof.
  cbn in *. intros G D GDG s Hf Hd. split; intros H C; specialize (Hd x) as [Hlr Hrl];
  (apply Hlr; [| eapply fv_fill; [| right]]; eassumption).
Qed.
Hint Resolve fill_disjoint_r : core.

Theorem wf_ctx_hole : forall GD,
  WFContext GD ->
  forall G D,
  Fill G D GD ->
  WFHole G.
Proof.
  intros GD Hc G D Hf. generalize dependent Hc.
  induction Hf; intros; [constructor | | | |]; sinvert Hc; constructor; try apply IHHf; try assumption;
  try (eapply fill_disjoint_l; eassumption); eapply fill_disjoint_r; eassumption.
Qed.
Hint Resolve wf_ctx_hole : core.

Theorem wf_ctx_plug : forall GD,
  WFContext GD ->
  forall G D,
  Fill G D GD ->
  WFContext D.
Proof.
  intros GD Hc G D Hf. generalize dependent Hc.
  induction Hf; intros; try (apply IHHf; sinvert Hc); assumption.
Qed.
Hint Resolve wf_ctx_plug : core.

Lemma wf_ctx_fill : forall G D GD,
  Fill G D GD ->
  WFHole G ->
  WFContext D ->
  DisjointSets (fv G) (fv D) ->
  WFContext GD.
Proof.
  intros G D GD Hf HG HD Hd. generalize dependent D. generalize dependent GD.
  induction HG; cbn in *; intros; sinvert Hf; [assumption | | | |];
  constructor; try assumption (* 1/3 *); try eapply IHHG; clear IHHG; try eassumption;
  apply fv_fill in H5; (* <-- this is the crucial move! *) sfirstorder.
Qed.
Hint Resolve wf_ctx_fill : core.

Lemma fill_wf_disjoint : forall G D GD,
  Fill G D GD ->
  WFContext GD ->
  DisjointSets (fv G) (fv D).
Proof.
  intros G D GD Hf Hwf.
  cbn in *. intro x. assert (Hiff := fv_fill _ _ _ Hf x). cbn in Hiff.
  generalize dependent D. generalize dependent GD. induction G; cbn in *; intros; [sfirstorder | | | |];
  sinvert Hf; sinvert Hwf; assert (Hfv := fv_fill _ _ _ H3); cbn in *; specialize (H4 x) as [Hlr Hrl];
  (edestruct IHG as [IH1 IH2]; [| eassumption | apply fv_fill |]; [assumption | assumption |]; sfirstorder).
Qed.
Hint Resolve fill_wf_disjoint : core.

Theorem wf_hole_iff : forall G D GD,
  Fill G D GD -> (
    WFContext GD <-> (
      WFHole G /\
      WFContext D /\
      DisjointSets (fv G) (fv D))).
Proof.
  intros G D GD Hf. split; [intro Hwf | intros [HG [HD Hd]]].
  - split; [| split]; [eapply wf_ctx_hole | eapply wf_ctx_plug | eapply fill_wf_disjoint]; eassumption.
  - eapply wf_ctx_fill; eassumption.
Qed.

Theorem wf_fill : forall h d,
  WFContext (fill h d) <-> (WFHole h /\ WFContext d /\ DisjointSets (fv h) (fv d)).
Proof.
  intros h d.
  remember (fill h d) as g.
  apply reflect_fill in Heqg.
  hauto l: on use: wf_hole_iff.
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
