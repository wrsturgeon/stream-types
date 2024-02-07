From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Context
  Eqb
  FV
  Terms
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

Instance fv_hole_inst : FV hole := { fv := fv_hole }.

Fixpoint fv_hole_li h :=
  match h with
  | HoleHere =>
      nil
  | HoleCommaL h c
  | HoleCommaR c h
  | HoleSemicL h c
  | HoleSemicR c h =>
      List.app (fv_ctx_li c) (fv_hole_li h)
  end.

Lemma reflect_fv_hole : forall h x,
  Bool.reflect (fv h x) (lcontains x (fv_hole_li h)).
Proof.
  induction h; cbn in *; intros.
  - constructor. intros [].
  - rewrite lcontains_app. specialize (IHh x). sinvert IHh. {
      rewrite Bool.orb_true_r. constructor. right. assumption. }
    destruct (lcontains_in x (fv_ctx_li g)); constructor. {
      left. apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)).
      apply (Bool.reflect_iff _ _ (lcontains_in _ _)). assumption. }
    intros [C | C]; [| tauto]. apply n. apply (Bool.reflect_iff _ _ (lcontains_in _ _)).
    apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)). assumption.
  - rewrite lcontains_app. specialize (IHh x). sinvert IHh. {
      rewrite Bool.orb_true_r. constructor. right. assumption. }
    destruct (lcontains_in x (fv_ctx_li g)); constructor. {
      left. apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)).
      apply (Bool.reflect_iff _ _ (lcontains_in _ _)). assumption. }
    intros [C | C]; [| tauto]. apply n. apply (Bool.reflect_iff _ _ (lcontains_in _ _)).
    apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)). assumption.
  - rewrite lcontains_app. specialize (IHh x). sinvert IHh. {
      rewrite Bool.orb_true_r. constructor. right. assumption. }
    destruct (lcontains_in x (fv_ctx_li g)); constructor. {
      left. apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)).
      apply (Bool.reflect_iff _ _ (lcontains_in _ _)). assumption. }
    intros [C | C]; [| tauto]. apply n. apply (Bool.reflect_iff _ _ (lcontains_in _ _)).
    apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)). assumption.
  - rewrite lcontains_app. specialize (IHh x). sinvert IHh. {
      rewrite Bool.orb_true_r. constructor. right. assumption. }
    destruct (lcontains_in x (fv_ctx_li g)); constructor. {
      left. apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)).
      apply (Bool.reflect_iff _ _ (lcontains_in _ _)). assumption. }
    intros [C | C]; [| tauto]. apply n. apply (Bool.reflect_iff _ _ (lcontains_in _ _)).
    apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)). assumption.
Qed.
Hint Resolve reflect_fv_hole : core.

(* Sanity check: *)
Theorem fv_hole_plug : forall h,
  SetEq (fv_hole h) (fv (fill h CtxEmpty)).
Proof. induction h; intros; split; sfirstorder. Qed.
Hint Resolve fv_hole_plug : core.

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

Fixpoint ctx_lookup G x :=
  match G with
  | CtxEmpty =>
      None
  | CtxHasTy z t =>
      if eqb x z then Some t else None
  | CtxComma lhs rhs
  | CtxSemic lhs rhs =>
      match ctx_lookup lhs x with Some t => Some t | None => ctx_lookup rhs x end
  end.

Theorem ctx_lookup_fv : forall G x,
  ctx_lookup G x = None <-> ~fv G x.
Proof.
  induction G; cbn in *; intros.
  - tauto.
  - destruct (String.eqb_spec x id). { subst. split; intros. { discriminate H. } contradiction H. reflexivity. }
    split. { symmetry. assumption. } reflexivity.
  - destruct (ctx_lookup G1 x) eqn:E1.
    + split; intros. { discriminate H. } apply Decidable.not_or in H as [H _].
      apply IHG1 in H. rewrite E1 in H. discriminate H.
    + split. { intros E2 C. apply IHG1 in E1. apply IHG2 in E2. tauto. } intro H. apply IHG2. tauto.
  - destruct (ctx_lookup G1 x) eqn:E1.
    + split; intros. { discriminate H. } apply Decidable.not_or in H as [H _].
      apply IHG1 in H. rewrite E1 in H. discriminate H.
    + split. { intros E2 C. apply IHG1 in E1. apply IHG2 in E2. tauto. } intro H. apply IHG2. tauto.
Qed.

Theorem ctx_lookup_fill : forall GD x t,
  WFContext GD ->
  (ctx_lookup GD x = Some t <-> exists G, Fill G (CtxHasTy x t) GD).
Proof.
  intros GD x t Hw. split.
  - generalize dependent t. generalize dependent x. induction GD; cbn in *; intros.
    + discriminate H.
    + destruct (String.eqb_spec x id); sinvert H. eexists. constructor.
    + sinvert Hw. specialize (IHGD1 H2). specialize (IHGD2 H3).
      destruct (ctx_lookup GD1 x) eqn:E1; [sinvert H; apply IHGD1 in E1 as [G HG] | apply IHGD2 in H as [G HG]];
      eexists; [apply FillCommaL | apply FillCommaR]; eassumption.
    + sinvert Hw. specialize (IHGD1 H2). specialize (IHGD2 H3).
      destruct (ctx_lookup GD1 x) eqn:E1; [sinvert H; apply IHGD1 in E1 as [G HG] | apply IHGD2 in H as [G HG]];
      eexists; [apply FillSemicL | apply FillSemicR]; eassumption.
  - intros [G HG]. generalize dependent t. generalize dependent x. generalize dependent GD.
    induction G; intros; sinvert HG; cbn in *.
    + rewrite eqb_refl. reflexivity.
    + sinvert Hw. apply IHG in H3; [| assumption]. rewrite H3. reflexivity.
    + sinvert Hw. specialize (IHG _ H2 _ _ H3). rewrite IHG. assert (Hf := fv_fill _ _ _ H3).
      assert (E : ctx_lookup g x = None). { apply ctx_lookup_fv. apply H4. apply Hf. left. reflexivity. }
      rewrite E. reflexivity.
    + sinvert Hw. apply IHG in H3; [| assumption]. rewrite H3. reflexivity.
    + sinvert Hw. specialize (IHG _ H2 _ _ H3). rewrite IHG. assert (Hf := fv_fill _ _ _ H3).
      assert (E : ctx_lookup g x = None). { apply ctx_lookup_fv. apply H4. apply Hf. left. reflexivity. }
      rewrite E. reflexivity.
Qed.
Hint Resolve ctx_lookup_fill : core.

Fixpoint poke G x :=
  match G with
  | CtxEmpty =>
      None
  | CtxHasTy z t =>
      if eqb x z then Some (pair t HoleHere) else None
  | CtxComma lhs rhs =>
      match poke lhs x with
      | Some (pair t h) => Some (pair t (HoleCommaL h rhs))
      | None =>
          match poke rhs x with
          | Some (pair t h) => Some (pair t (HoleCommaR lhs h))
          | None => None
          end
      end
  | CtxSemic lhs rhs =>
      match poke lhs x with
      | Some (pair t h) => Some (pair t (HoleSemicL h rhs))
      | None =>
          match poke rhs x with
          | Some (pair t h) => Some (pair t (HoleSemicR lhs h))
          | None => None
          end
      end
  end.

Lemma poke_fill : forall GD x t G,
  poke GD x = Some (pair t G) ->
  Fill G (CtxHasTy x t) GD.
Proof.
  induction GD; cbn in *; intros; [discriminate H | destruct (String.eqb_spec x id); sinvert H; constructor | |];
  destruct (poke GD1 x) as [[t1 h1] |] eqn:E1; destruct (poke GD2 x) as [[t2 h2] |] eqn:E2; sinvert H;
  constructor; try apply IHGD1; try apply IHGD2; assumption.
Qed.

Lemma fill_poke : forall GD x t G,
  ~fv G x ->
  Fill G (CtxHasTy x t) GD ->
  poke GD x = Some (pair t G).
Proof.
  induction GD; cbn in *; intros;
  [sinvert H0 | destruct (String.eqb_spec x id); sinvert H0; [reflexivity | tauto] | |].
  - destruct (poke GD1 x) as [[t1 h1] |] eqn:E1. {
      sinvert H0; cbn in H; apply Decidable.not_or in H as [H1 H2].
      - erewrite IHGD1 in E1; [| | eassumption]; [| assumption]. sinvert E1. reflexivity.
      - assert (Hp := poke_fill _ _ _ _ E1). assert (Hf := fv_fill _ _ _ Hp).
        contradiction H1. apply Hf. left. reflexivity. }
    destruct (poke GD2 x) as [[t2 h2] |] eqn:E2. {
      sinvert H0; cbn in H; apply Decidable.not_or in H as [H1 H2].
      - erewrite IHGD1 in E1; [| | eassumption]; [| assumption]. discriminate E1.
      - erewrite IHGD2 in E2; [| | eassumption]; [| assumption]. sinvert E2. reflexivity. }
    sinvert H0; cbn in H; apply Decidable.not_or in H as [H1 H2];
    [specialize (IHGD1 _ _ _ H2 H4) | specialize (IHGD2 _ _ _ H2 H4)]; congruence.
  - destruct (poke GD1 x) as [[t1 h1] |] eqn:E1. {
      sinvert H0; cbn in H; apply Decidable.not_or in H as [H1 H2].
      - erewrite IHGD1 in E1; [| | eassumption]; [| assumption]. sinvert E1. reflexivity.
      - assert (Hp := poke_fill _ _ _ _ E1). assert (Hf := fv_fill _ _ _ Hp).
        contradiction H1. apply Hf. left. reflexivity. }
    destruct (poke GD2 x) as [[t2 h2] |] eqn:E2. {
      sinvert H0; cbn in H; apply Decidable.not_or in H as [H1 H2].
      - erewrite IHGD1 in E1; [| | eassumption]; [| assumption]. discriminate E1.
      - erewrite IHGD2 in E2; [| | eassumption]; [| assumption]. sinvert E2. reflexivity. }
    sinvert H0; cbn in H; apply Decidable.not_or in H as [H1 H2];
    [specialize (IHGD1 _ _ _ H2 H4) | specialize (IHGD2 _ _ _ H2 H4)]; congruence.
Qed.

(* Carve out the smallest hole (assuming WF) that binds all these variables *)
(* TODO: don't compute FVs arbitrarily many times, then convince Coq it's the same function *)
Fixpoint zoom_in (free : list _ (* ouch *)) G :=
  match G with
  | CtxEmpty | CtxHasTy _ _ => pair HoleHere G
  | CtxComma lhs rhs =>
      if lsubset free (fv_ctx_li lhs) then
        let (g, d) := zoom_in free lhs in pair (HoleCommaL g rhs) d else
      if lsubset free (fv_ctx_li rhs) then
        let (g, d) := zoom_in free rhs in pair (HoleCommaR lhs g) d else
      pair HoleHere G
  | CtxSemic lhs rhs =>
      if lsubset free (fv_ctx_li lhs) then
        let (g, d) := zoom_in free lhs in pair (HoleSemicL g rhs) d else
      if lsubset free (fv_ctx_li rhs) then
        let (g, d) := zoom_in free rhs in pair (HoleSemicR lhs g) d else
      pair HoleHere G
  end.

Lemma zoom_in_full : forall GD free,
  let (G, D) := zoom_in free GD in
  Fill G D GD.
Proof.
  induction GD; cbn in *; intros; try constructor; specialize (IHGD1 free); specialize (IHGD2 free);
  destruct (zoom_in free GD1) as [G1 D1]; destruct (zoom_in free GD2) as [G2 D2];
  destruct (lsubset free (fv_ctx_li GD1)) eqn:E1; try (constructor; assumption);
  destruct (lsubset free (fv_ctx_li GD2)) eqn:E2; constructor; assumption.
Qed.
Hint Resolve zoom_in_full : core.

Lemma zoom_in_full_fn : forall GD free,
  let (G, D) := zoom_in free GD in
  fill G D = GD.
Proof.
  induction GD; cbn in *; intros; try reflexivity; specialize (IHGD1 free); specialize (IHGD2 free);
  destruct (zoom_in free GD1) as [G1 D1]; destruct (zoom_in free GD2) as [G2 D2];
  destruct (lsubset free (fv_ctx_li GD1)) eqn:E1; cbn; f_equal; try assumption;
  destruct (lsubset free (fv_ctx_li GD2)) eqn:E2; cbn; f_equal; assumption.
Qed.
Hint Resolve zoom_in_full_fn : core.

Theorem zoom_in_fv : forall GD free,
  let (G, D) := zoom_in free GD in
  forall x,
  List.In x free ->
  fv GD x ->
  fv D x.
Proof.
  induction GD; cbn in *; intros.
  - destruct H0.
  - assumption.
  - specialize (IHGD1 free). specialize (IHGD2 free).
    destruct (zoom_in free GD1) as [G1 D1] eqn:E1. destruct (zoom_in free GD2) as [G2 D2] eqn:E2.
    destruct (lsubset_incl free (fv_ctx_li GD1)). {
      intros. apply IHGD1; [assumption |]. destruct H0; [assumption |].
      apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)). apply (Bool.reflect_iff _ _ (lcontains_in _ _)).
      apply i. assumption. }
    destruct (lsubset_incl free (fv_ctx_li GD2)); intros; [| assumption].
    apply IHGD2; [assumption |]. destruct H0; [| assumption].
    apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)). apply (Bool.reflect_iff _ _ (lcontains_in _ _)).
    apply i. assumption.
  - specialize (IHGD1 free). specialize (IHGD2 free).
    destruct (zoom_in free GD1) as [G1 D1] eqn:E1. destruct (zoom_in free GD2) as [G2 D2] eqn:E2.
    destruct (lsubset_incl free (fv_ctx_li GD1)). {
      intros. apply IHGD1; [assumption |]. destruct H0; [assumption |].
      apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)). apply (Bool.reflect_iff _ _ (lcontains_in _ _)).
      apply i. assumption. }
    destruct (lsubset_incl free (fv_ctx_li GD2)); intros; [| assumption].
    apply IHGD2; [assumption |]. destruct H0; [| assumption].
    apply (Bool.reflect_iff _ _ (reflect_fv_ctx _ _)). apply (Bool.reflect_iff _ _ (lcontains_in _ _)).
    apply i. assumption.
Qed.

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
