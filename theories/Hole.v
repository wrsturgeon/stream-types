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

Fixpoint fill h D :=
  match h with
  | HoleHere => D
  | HoleCommaL lhs rhs => CtxComma (fill lhs D) rhs
  | HoleCommaR lhs rhs => CtxComma lhs (fill rhs D)
  | HoleSemicL lhs rhs => CtxSemic (fill lhs D) rhs
  | HoleSemicR lhs rhs => CtxSemic lhs (fill rhs D)
  end.

Inductive Fill : hole -> context -> context -> Prop :=
  | FillHere : forall g,
      Fill HoleHere g g
  | FillCommaL : forall d h g hd,
      Fill h d hd ->
      Fill (HoleCommaL h g) d (CtxComma hd g)
  | FillCommaR : forall d g h hd,
      Fill h d hd ->
      Fill (HoleCommaR g h) d (CtxComma g hd)
  | FillSemicL : forall d h g hd,
      Fill h d hd ->
      Fill (HoleSemicL h g) d (CtxSemic hd g)
  | FillSemicR : forall d g h hd,
      Fill h d hd ->
      Fill (HoleSemicR g h) d (CtxSemic g hd)
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

Theorem fill_reflect_fun : forall h d, exists hd, Fill h d hd.
Proof.
Admitted.

(* TODO: will *)
Theorem fill_reflect_inj : forall h d d' hd,
  Fill h d hd ->
  Fill h d' hd ->
  d = d'.
Proof.
Admitted.

(* TODO: will. This one is cute: if your context is well formed,
there is at most one way to arrive at it by filling a hole with x.
I'm pretty sure this fact, for all variables is equivalent to WFContext! *)
Theorem fill_reflect_var_localize : forall h h' hd x s s',
  WFContext hd ->
  Fill h (CtxHasTy x s) hd ->
  Fill h' (CtxHasTy x s') hd ->
  h = h' /\ s = s'.
Proof.
Admitted.

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
Hint Resolve fv_hole_plug : core.

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
      DisjointSets (fv g) (fv h) ->
      WFHole (HoleCommaR g h)
  | WFHoleSemicL : forall h g,
      WFHole h ->
      WFContext g ->
      DisjointSets (fv h) (fv g) ->
      WFHole (HoleSemicL h g)
  | WFHoleSemicR : forall h g,
      WFHole h ->
      WFContext g ->
      DisjointSets (fv g) (fv h) ->
      WFHole (HoleSemicR g h)
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
Hint Resolve wf_hole_iff : core.

Theorem wf_fill : forall h d,
  WFContext (fill h d) <-> (WFHole h /\ WFContext d /\ DisjointSets (fv h) (fv d)).
Proof.
  intros h d.
  remember (fill h d) as g.
  apply reflect_fill in Heqg.
  hauto l: on use: wf_hole_iff.
Qed.
Hint Resolve wf_fill : core.

Theorem wf_fill_reflect : forall h d hd,
  Fill h d hd ->
  WFContext hd <-> (WFHole h /\ WFContext d /\ DisjointSets (fv h) (fv d)).
Proof.
intros.
eapply reflect_fill in H.
hauto l: on use: wf_fill.
Qed.
Hint Resolve wf_fill_reflect : core.

(* TODO: delete everything below this line *)

Lemma set_minus_fill_cancel : forall G z r,
  ~fv G z ->
  SetEq
    (set_minus (fv (fill G (CtxHasTy z r))) (singleton_set z))
    (fv G).
Proof.
  cbn. intros G z r Hz x. split.
  - intros [Hfv Hne]. apply fv_fill_fn in Hfv as [H | H]; cbn in H. { contradiction Hne. } assumption.
  - intro H. split. { apply fv_fill_fn. cbn. right. assumption. } intro. subst. contradiction Hz.
Qed.
Hint Resolve set_minus_fill_cancel : core.

(* In plain English:
 * Given a context G with a hole and a variable z (used to require that z not in G, but not actually necessary),
 * if you fill G with either (x: s; y: t) or (x: s, y: t),
 * the resulting free variables are exactly the free variables of G plus x and y.
 * In other words, **this is just a special case of `fv_fill`.** *)
Theorem hmm : forall G x y (* z *) s t ctr,
  (ctr = CtxComma \/ ctr = CtxSemic) ->
  SetEq
    (set_union (fv G) (set_union (singleton_set x) (singleton_set y)))
    (fv (fill G (ctr (CtxHasTy x s) (CtxHasTy y t)))).
Proof.
  cbn. intros. remember (fill G (ctr (CtxHasTy x s) (CtxHasTy y t))) as Gxy eqn:E.
  apply reflect_fill in E. apply fv_fill in E. split; intros.
  - repeat destruct H0; [eapply E; right; assumption | |];
    destruct H; subst; apply E; left; try (left; reflexivity); right; reflexivity.
  - apply E in H0. clear E. destruct H; subst; sfirstorder.
Qed.
Hint Resolve hmm : core.

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
Hint Resolve hmm' : core.

Theorem hmm'_reflect : forall G Gz Gxy x y z s t r ctr,
  (ctr = CtxComma \/ ctr = CtxSemic) ->
  x <> y ->
  ~(fv G x) ->
  ~(fv G y) ->
  Fill G (CtxHasTy z r) Gz ->
  Fill G (ctr (CtxHasTy x s) (CtxHasTy y t)) Gxy ->
  WFContext Gz ->
  WFContext Gxy.
Proof.
 intros.
 eapply reflect_fill in H3.
 eapply reflect_fill in H4.
 rewrite -> H3 in *.
 rewrite -> H4 in *.
 eapply hmm'; eauto.
Qed.
Hint Resolve hmm'_reflect : core.

Fixpoint hole_compose (h : hole) (h' : hole) : hole :=
  match h with
  | HoleHere => h'
  | HoleCommaL lhs rhs => HoleCommaL (hole_compose lhs h') rhs
  | HoleCommaR lhs rhs => HoleCommaR lhs (hole_compose rhs h')
  | HoleSemicL lhs rhs => HoleSemicL (hole_compose lhs h') rhs
  | HoleSemicR lhs rhs => HoleSemicR lhs (hole_compose rhs h')
  end.

(* TODO: will *) (* this will also need another tehorem about its derivatives, unfortunately. *)

Theorem hole_compose_fill : forall h h' d hh'd,
  Fill (hole_compose h h') d hh'd <-> (exists h'd, Fill h' d h'd /\ Fill h h'd hh'd).
Proof.
Admitted.


Theorem hole_compose_fv : forall h h',
  SetEq (fv (hole_compose h h')) (set_union (fv h) (fv h'))
.
Proof.
Admitted.
