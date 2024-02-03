From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Derivative
  Environment
  FV
  Hole
  Inert
  Prefix
  Sets.

(* Definition B.34 *)
(* Argument order designed for notation: (Subcontext A B) === (A <: B) *)
Inductive Subcontext : context -> context -> Prop :=
  | SubRefl : forall g,
      Subcontext g g
  | SubCommaExc : forall g d,
      Subcontext (CtxComma g d) (CtxComma d g)
  | SubCommaWkn : forall g d,
      Subcontext (CtxComma g d) g
  (* don't need right-hand comma weakening b/c we have exchange *)
  | SubSemicWkn1 : forall g d,
      Subcontext (CtxSemic g d) g
  | SubSemicWkn2 : forall g d,
      Subcontext (CtxSemic g d) d
  | SubCommaUnit : forall g,
      Subcontext g (CtxComma g CtxEmpty)
  | SubSemicUnit1 : forall g,
      Subcontext g (CtxSemic g CtxEmpty)
  | SubSemicUnit2 : forall g,
      Subcontext g (CtxSemic CtxEmpty g)
  | SubCong : forall d d' g gd gd',
      Fill g d gd ->
      Fill g d' gd' ->
      Subcontext d d' ->
      Subcontext gd gd'
  .
Hint Constructors Subcontext : core.

Theorem subcontext_fv_subset : forall g g',
  Subcontext g g' ->
  Subset (fv g') (fv g).
Proof.
  intros. induction H; cbn in *; intros; [| | | | | | | | shelve]; sfirstorder.
  (* Only interesting case is `Fill`, covered below: *)
  Unshelve. eapply fv_fill; [eassumption |]. apply fv_fill in H. apply fv_fill in H0. cbn in *.
  apply H0 in H2. destruct H2; [| right; assumption]. left. apply IHSubcontext. assumption.
Qed.
Hint Resolve subcontext_fv_subset : core.

Lemma fill_preserves_env : forall (d d' : context) (g : hole) (gd gd' : context),
  Fill g d gd ->
  Fill g d' gd' ->
  (forall n : env, EnvTyped n d -> EnvTyped n d') ->
  forall n : env,
  Agree Inert n n (fv d) (fv d') ->
  EnvTyped n gd ->
  EnvTyped n gd'.
Proof.
  intros d d' g gd gd' Hf Hf' Hi n [Hm He] Ht.
  generalize dependent gd'. generalize dependent d'. generalize dependent n.
  induction Hf; cbn in *; intros.
  - sinvert Hf'. hauto l: on.
  - sinvert Hf'. sinvert Ht. clear Hf. sauto lq: on rew: off.
  - sinvert Hf'. sinvert Ht. clear Hf. sauto lq: on rew: off.
  - sinvert Hf'. sinvert Ht. constructor; [clear H5 H4; hauto l: on | assumption |].
    destruct H5; [left; assumption |]. right. specialize (He eq_refl).
    eapply prop_on_fill_iff in Hf. eapply prop_on_fill_iff in H3. clear IHHf Hi He H1 H4. sfirstorder.
  - sinvert Hf'. sinvert Ht. constructor; [assumption | hauto l: on |].
    destruct H5; [| right; assumption]. left. specialize (He eq_refl).
    eapply prop_on_fill_iff in Hf. eapply prop_on_fill_iff in H3. clear IHHf Hi Hm H1 H4. sfirstorder.
Qed.
Hint Resolve fill_preserves_env : core.

(* Theorem B.35 *)
(* NOTE: had to strengthen this to, carry along the agreement. *)
Theorem sub_preserves_env : forall n G D,
  EnvTyped n G ->
  Subcontext G D ->
  EnvTyped n D /\ Agree Inert n n (fv G) (fv D).
Proof.
  intros n G D He Hs. generalize dependent n. induction Hs; intros.
  - repeat split; intros; eassumption.
  - sinvert He. repeat split; sfirstorder.
  - sinvert He. repeat split; sfirstorder.
  - sinvert He. repeat split; sfirstorder.
  - sinvert He. repeat split; sfirstorder.
  - repeat constructor; sfirstorder.
  - repeat constructor; sfirstorder.
  - repeat constructor; sfirstorder.
  - assert (A := maps_to_hole_reflect _ _ _ _ H He). assert (IH := IHHs _ A). destruct IH as [IH1 IH2]. split.
    + eapply fill_preserves_env; [ | eassumption | | eassumption | ]; try eassumption. apply IHHs.
    + split; intros; (eapply prop_on_subset; [| eassumption]);
      apply subcontext_fv_subset; econstructor; eassumption.
Qed.
Hint Resolve sub_preserves_env : core.

(* Theorem B.36 *)
Theorem deriv_subctx : forall G D,
  Subcontext G D ->
  forall n G' D',
  ContextDerivative n G G' ->
  ContextDerivative n D D' ->
  Subcontext G' D'.
Proof.
  intros G D Hs n G' D' HG HD. generalize dependent n.
  generalize dependent G'. generalize dependent D'. induction Hs; cbn in *; intros.
  - assert (E := context_derivative_det _ _ _ _ HG HD). subst. constructor.
  - sinvert HG. sinvert HD. assert (E := context_derivative_det _ _ _ _ H2 H6). subst.
    assert (E := context_derivative_det _ _ _ _ H3 H4). subst. constructor.
  - sinvert HG. assert (E := context_derivative_det _ _ _ _ HD H2). subst. constructor.
  - sinvert HG. assert (E := context_derivative_det _ _ _ _ HD H2). subst. constructor.
  - sinvert HG. assert (E := context_derivative_det _ _ _ _ HD H4). subst. constructor.
  - sinvert HD. sinvert H4. assert (E := context_derivative_det _ _ _ _ HG H2). subst. constructor.
  - sinvert HD. sinvert H4. assert (E := context_derivative_det _ _ _ _ HG H2). subst. constructor.
  - sinvert HD. sinvert H2. assert (E := context_derivative_det _ _ _ _ HG H4). subst. constructor.
  - generalize dependent d. generalize dependent d'. generalize dependent gd.
    generalize dependent gd'. generalize dependent D'. generalize dependent G'.
    generalize dependent n. induction g; cbn in *; intros; sinvert H0; sinvert H;
    [eapply IHHs; eassumption | | | |]; sinvert HD; sinvert HG;
    try (assert (E := context_derivative_det _ _ _ _ H6 H8));
    try (assert (E := context_derivative_det _ _ _ _ H2 H3));
    subst; sauto lq: on.
Qed.
Hint Resolve deriv_subctx : core.
