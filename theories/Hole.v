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

Theorem reflect_fill : forall h y c,
  c = fill h y <-> Fill h y c.
Proof.
  split; intros.
  - subst. generalize dependent y. induction h; intros; cbn in *; constructor; apply IHh.
  - induction H; cbn; try rewrite IHFill; reflexivity.
Qed.
Hint Resolve reflect_fill : core.

Theorem fill_reflect_fun : forall h d, exists hd, Fill h d hd.
Proof. intros. exists (fill h d). apply reflect_fill. reflexivity. Qed.

Theorem fill_reflect_inj : forall h d d' hd,
  Fill h d hd ->
  Fill h d' hd ->
  d = d'.
Proof.
  induction h; intros d d' hd Hf Hf'; sinvert Hf; sinvert Hf';
  [reflexivity | | | |]; eapply IHh; eassumption.
Qed.

(* had to move `fill_reflect_var_localize` after `fv_fill` *)

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

Lemma fv_fill' : forall h plug ctx,
  Fill h plug ctx ->
  SetEq (set_union (fv plug) (fv h)) (fv ctx).
Proof. intros. induction H; sfirstorder. Qed.
Hint Resolve fv_fill : core.

Lemma fv_fill_fn : forall h plug,
  SetEq (fv_ctx (fill h plug)) (set_union (fv plug) (fv h)).
Proof. intros. remember (fill h plug) as ctx eqn:E. apply reflect_fill in E. apply fv_fill. assumption. Qed.
Hint Resolve fv_fill_fn : core.

(* This one is cute: if your context is well formed,
 * there is at most one way to arrive at it by filling a hole with x.
 * I'm pretty sure this fact, for all variables is equivalent to WFContext! *)
Theorem fill_reflect_var_localize : forall h h' hd x s s',
  WFContext hd ->
  Fill h (CtxHasTy x s) hd ->
  Fill h' (CtxHasTy x s') hd ->
  h = h' /\ s = s'.
Proof.
  induction h; intros h' hd x s s' Hw Hf Hf'; sinvert Hf.
  - sinvert Hf'. split; reflexivity.
  - sinvert Hw. sinvert Hf'. { specialize (IHh _ _ _ _ _ H1 H3 H6) as [IH1 IH2]. subst. split; reflexivity. }
    apply fv_fill in H3. apply fv_fill in H6. specialize (H3 x). specialize (H6 x). specialize (H4 x) as [D1 D2].
    contradiction D1; [apply H3 | apply H6]; left; reflexivity.
  - sinvert Hw. sinvert Hf'. 2: { specialize (IHh _ _ _ _ _ H2 H3 H6) as [IH1 IH2]. subst. split; reflexivity. }
    apply fv_fill in H3. apply fv_fill in H6. specialize (H3 x). specialize (H6 x). specialize (H4 x) as [D1 D2].
    contradiction D1; [apply H6 | apply H3]; left; reflexivity.
  - sinvert Hw. sinvert Hf'. { specialize (IHh _ _ _ _ _ H1 H3 H6) as [IH1 IH2]. subst. split; reflexivity. }
    apply fv_fill in H3. apply fv_fill in H6. specialize (H3 x). specialize (H6 x). specialize (H4 x) as [D1 D2].
    contradiction D1; [apply H3 | apply H6]; left; reflexivity.
  - sinvert Hw. sinvert Hf'. 2: { specialize (IHh _ _ _ _ _ H2 H3 H6) as [IH1 IH2]. subst. split; reflexivity. }
    apply fv_fill in H3. apply fv_fill in H6. specialize (H3 x). specialize (H6 x). specialize (H4 x) as [D1 D2].
    contradiction D1; [apply H6 | apply H3]; left; reflexivity.
Qed.

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

Theorem wf_fill_reflect' : forall h d hd,
  Fill h d hd ->
  WFContext hd -> (WFHole h /\ WFContext d /\ DisjointSets (fv h) (fv d)).
Proof.
best use:wf_fill_reflect.
Qed.
Hint Resolve wf_fill_reflect : core.

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

Inductive HoleCompose : hole -> hole -> hole -> Prop :=
  | HCompHere : forall g,
      HoleCompose HoleHere g g
  | HCompCommaL : forall d h g hd,
      HoleCompose h d hd ->
      HoleCompose (HoleCommaL h g) d (HoleCommaL hd g)
  | HCompCommaR : forall d g h hd,
      HoleCompose h d hd ->
      HoleCompose (HoleCommaR g h) d (HoleCommaR g hd)
  | HCompSemicL : forall d h g hd,
      HoleCompose h d hd ->
      HoleCompose (HoleSemicL h g) d (HoleSemicL hd g)
  | HCompSemicR : forall d g h hd,
      HoleCompose h d hd ->
      HoleCompose (HoleSemicR g h) d (HoleSemicR g hd)
  .
Hint Constructors HoleCompose : core.

Theorem reflect_hole_compose : forall h y c,
  c = hole_compose h y <-> HoleCompose h y c.
Proof.
  split; intros.
  - subst. generalize dependent y. induction h; intros; cbn in *; constructor; apply IHh.
  - induction H; cbn; try rewrite IHHoleCompose; reflexivity.
Qed.
Hint Resolve reflect_hole_compose : core.

Theorem hole_compose_fill : forall h h' hh',
  HoleCompose h h' hh' ->
  forall d hh'd,
  Fill hh' d hh'd <-> (exists h'd, Fill h' d h'd /\ Fill h h'd hh'd).
Proof.
  intros h h' hh' Hh. induction Hh; cbn in *; intros.
  - split. { eexists. split. { eassumption. } constructor. } intros [h'd [H1 H2]]. sinvert H2. assumption.
  - split. { intro H. sinvert H. apply IHHh in H4 as [h'd [H1 H2]]. eexists. repeat constructor; eassumption. }
    intros [h'd [H1 H2]]. sinvert H2. constructor. apply IHHh. eexists. split; eassumption.
  - split. { intro H. sinvert H. apply IHHh in H4 as [h'd [H1 H2]]. eexists. repeat constructor; eassumption. }
    intros [h'd [H1 H2]]. sinvert H2. constructor. apply IHHh. eexists. split; eassumption.
  - split. { intro H. sinvert H. apply IHHh in H4 as [h'd [H1 H2]]. eexists. repeat constructor; eassumption. }
    intros [h'd [H1 H2]]. sinvert H2. constructor. apply IHHh. eexists. split; eassumption.
  - split. { intro H. sinvert H. apply IHHh in H4 as [h'd [H1 H2]]. eexists. repeat constructor; eassumption. }
    intros [h'd [H1 H2]]. sinvert H2. constructor. apply IHHh. eexists. split; eassumption.
Qed.
Hint Resolve hole_compose_fill : core.

Theorem hole_compose_fv : forall h h' hh',
  HoleCompose h h' hh' ->
  SetEq (fv hh') (set_union (fv h) (fv h')).
Proof.
  intros. induction H; cbn; intros.
  - split; intros. { right. assumption. } destruct H as [[] |]. assumption.
  - split; intros.
    + destruct H0. { left. left. assumption. }
      apply IHHoleCompose in H0. destruct H0. { left. right. assumption. } right. assumption.
    + destruct H0. { destruct H0. { left. assumption. } right. apply IHHoleCompose. left. assumption. }
      right. apply IHHoleCompose. right. assumption.
  - split; intros.
    + destruct H0. { left. left. assumption. }
      apply IHHoleCompose in H0. destruct H0. { left. right. assumption. } right. assumption.
    + destruct H0. { destruct H0. { left. assumption. } right. apply IHHoleCompose. left. assumption. }
      right. apply IHHoleCompose. right. assumption.
  - split; intros.
    + destruct H0. { left. left. assumption. }
      apply IHHoleCompose in H0. destruct H0. { left. right. assumption. } right. assumption.
    + destruct H0. { destruct H0. { left. assumption. } right. apply IHHoleCompose. left. assumption. }
      right. apply IHHoleCompose. right. assumption.
  - split; intros.
    + destruct H0. { left. left. assumption. }
      apply IHHoleCompose in H0. destruct H0. { left. right. assumption. } right. assumption.
    + destruct H0. { destruct H0. { left. assumption. } right. apply IHHoleCompose. left. assumption. }
      right. apply IHHoleCompose. right. assumption.
Qed.
Hint Resolve hole_compose_fv : core.

Theorem hole_compose_fv_fn : forall h h',
  SetEq (fv (hole_compose h h')) (set_union (fv h) (fv h')).
Proof.
  intros. remember (hole_compose h h') as hh' eqn:E. apply reflect_hole_compose in E.
  apply hole_compose_fv. assumption.
Qed.
Hint Resolve hole_compose_fv_fn : core.

Inductive HoleSubst (x : string) (y : string) : hole -> hole -> Prop :=
| HSCommaL1 : forall h h' g,
    HoleSubst x y h h' ->
    HoleSubst x y (HoleCommaL h g) (HoleCommaL h' g)
| HSCommaL2 : forall h g g',
    CtxSubst x y g g' ->
    HoleSubst x y (HoleCommaL h g) (HoleCommaL h g')
| HSCommaR1 : forall h h' g,
    HoleSubst x y h h' ->
    HoleSubst x y (HoleCommaR g h) (HoleCommaR g h')
| HSCommaR2 : forall h g g',
    CtxSubst x y g g' ->
    HoleSubst x y (HoleCommaR g h) (HoleCommaR g' h)
| HSSemicL1 : forall h h' g,
    HoleSubst x y h h' ->
    HoleSubst x y (HoleSemicL h g) (HoleSemicL h' g)
| HSSemicL2 : forall h g g',
    CtxSubst x y g g' ->
    HoleSubst x y (HoleSemicL h g) (HoleSemicL h g')
| HSSemicR1 : forall h h' g,
    HoleSubst x y h h' ->
    HoleSubst x y (HoleSemicR g h) (HoleSemicR g h')
| HSSemicR2 : forall h g g',
    CtxSubst x y g g' ->
    HoleSubst x y (HoleSemicR g h) (HoleSemicR g' h)
.

Theorem ctx_subst_exists_fill_exact : forall G G1 G2 x y s,
  Fill G (CtxHasTy y s) G1 ->
  Fill G (CtxHasTy x s) G2 ->
  CtxSubst x y G1 G2.
Proof.
intro G.
induction G; intros; sauto q: on.
Qed.

Theorem ctx_subst_fill_exists : forall G1 G2 x y,
  CtxSubst x y G1 G2 ->
  exists G s,
    Fill G (CtxHasTy y s) G1 /\
    Fill G (CtxHasTy x s) G2.
Proof.
  intros.
  induction H; sauto lq: on.
Qed.


Theorem ctx_subst_fill_other_hole : forall G G' x x0 y s h,
  Fill h (CtxHasTy x s) G ->
  CtxSubst x0 y G G' ->
  x <> y ->
  exists h', Fill h' (CtxHasTy x s) G'.
Proof.
  intros.
  generalize dependent x.
  generalize dependent h.
  generalize dependent s.
  induction H0; intros; sauto lq: on.
Qed.

Theorem ctx_subst_fill_arb : forall G D GD G0 x y,
  Fill G D GD ->
  CtxSubst x y GD G0 ->
  (exists G', 
    HoleSubst x y G G' /\
    Fill G' D G0 /\
    (forall D' GD', Fill G D' GD' ->
      exists G'D', Fill G' D' G'D' /\ CtxSubst x y GD' G'D'))
  \/
  (exists D', CtxSubst x y D D' /\ Fill G D' G0 /\
    (forall D0 D0' GD0,
       CtxSubst x y D0 D0' ->
       Fill G D0 GD0 ->
       exists GD0', Fill G D0' GD0' /\ CtxSubst x y GD0 GD0'
    )
  ).
Proof.
  intros.
  generalize dependent G0.
  generalize dependent x.
  generalize dependent y.
  induction H; intros.
  - best.
  - sinvert H0; sauto lq: on.
  - sinvert H0; sauto lq: on.
  - sinvert H0; sauto lq: on.
  - sinvert H0; sauto lq: on.
Qed.

(* TODO: will? *)
Theorem ctx_subst_fill_transport : forall G G1 G2 x y s,
  WFContext G1 ->
  CtxSubst x y G1 G2 ->
  Fill G (CtxHasTy y s) G1 ->
  Fill G (CtxHasTy x s) G2.
Proof.
Admitted.

Theorem hole_subst_found_fv : forall x y h h',
  HoleSubst x y h h' ->
  fv h y.
Proof.
  intros.
  induction H; hauto lq: on use:ctx_subst_found_fv.
Qed.

Theorem hole_subst_found_fv' : forall x y h h',
  HoleSubst x y h h' ->
  fv h' x.
Proof.
  intros.
  induction H; hauto lq: on use:ctx_subst_found_fv'.
Qed.

Theorem hole_subst_no_found_fv : forall z h' h x y,
  HoleSubst x y h h' ->
  ~fv h z ->
  z <> x ->
  ~fv h' z.
Proof.
intros. generalize dependent z.
induction H;sfirstorder use:ctx_subst_no_found_fv.
Qed.

Theorem hole_subst_not_in_fill : forall y d h x h' hd,
  Fill h d hd ->
  WFContext hd ->
  HoleSubst x y h h' ->
  ~fv d y.
Proof.
  intros.
  intro.
  edestruct wf_fill_reflect' as [A [B C]]; eauto.
  hauto lq: on use:hole_subst_found_fv.
Qed.