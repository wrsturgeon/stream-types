Require Import Coq.Program.Equality.
From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Inert
  Derivative
  Prefix
  Sets.

(* Definition B.34 *)
(* Argument order designed for notation: (Subcontext A B) === (A <: B) *)
Inductive Subcontext : context -> context -> Prop :=
  | SubCong : forall g d d' gd gd',
      Fill g d gd ->
      Fill g d' gd' ->
      Subcontext d d' ->
      Subcontext gd gd'
  | SubRefl : forall g,
      Subcontext g g
  | SubSngWkn : forall x s, Subcontext (CtxHasTy x s) CtxEmpty
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
  .
Hint Constructors Subcontext : core.




Theorem subcontext_fv_subset : forall g g',
  Subcontext g g' ->
  Subset (fv g') (fv g).
Proof.
  intros. induction H; cbn in *; intros; [shelve | | | | | | | | | ]; sfirstorder.
  (* Only interesting case is `Fill`, covered below: *)
  Unshelve. eapply fv_fill; [eassumption |]. apply fv_fill in H. apply fv_fill in H0. cbn in *.
  apply H0 in H2. destruct H2; [| right; assumption]. left. apply IHSubcontext. assumption.
Qed.
Hint Resolve subcontext_fv_subset : core.

Theorem subtcontext_wf : forall g g',
  Subcontext g g' -> WFContext g -> WFContext g'.
Proof.
intros.
dependent induction H.
- eapply wf_fill_reflect in H.
  eapply wf_fill_reflect. eauto. sfirstorder use:subcontext_fv_subset.
- sauto.
- sauto.
- sauto.
- sauto.
- sauto.
- sauto.
- sauto.
- sauto.
- sauto.
Qed.


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
Theorem sub_preserves_env : forall n G D,
  EnvTyped n G ->
  Subcontext G D ->
  EnvTyped n D /\ Agree Inert n n (fv G) (fv D).
Proof.
  intros n G D He Hs. generalize dependent n. induction Hs; intros.
  - assert (A := maps_to_hole_reflect _ _ _ _ H He). assert (IH := IHHs _ A). destruct IH as [IH1 IH2]. split.
    + eapply fill_preserves_env; [ | eassumption | | eassumption | ]; try eassumption. apply IHHs.
    + split; intros; (eapply prop_on_contains; [| eassumption]);
      apply subcontext_fv_subset; econstructor; eassumption.
  - repeat split; intros; eassumption.
  - sinvert He. repeat split; sfirstorder.
  - sinvert He. repeat split; sfirstorder.
  - sinvert He. repeat split; sfirstorder.
  - sinvert He. repeat split; sfirstorder.
  - sinvert He. repeat split; sfirstorder.
  - repeat constructor; sfirstorder.
  - repeat constructor; sfirstorder.
  - repeat constructor; sfirstorder.
Qed.

Theorem subctx_deriv : forall eta g1 g2 g1' g2',
  Subcontext g1 g2 ->
  ContextDerivative eta g1 g1' ->
  ContextDerivative eta g2 g2' ->
  Subcontext g1' g2'.
Proof.
intros.
generalize dependent g1'.
generalize dependent g2'.
dependent induction H; intros.
- edestruct (fill_derivative eta g d) as [dg [d_d [A [B [C D]]]]]; eauto.
  edestruct (fill_derivative eta g d') as [dg2 [d_d' [A' [B' [C' D']]]]]; eauto.
  assert (H00 : dg2 = dg) by sfirstorder use:hole_derivative_det.
  rewrite <- H00 in *.
  edestruct (D d' d_d' gd' eta); eauto.
- sauto lq:on use:context_derivative_det.
- sauto lq: on rew: off.
- sinvert H1; sinvert H0. sauto lq: on use:context_derivative_det.
- sinvert H0. sauto lq: on use:context_derivative_det.
- sinvert H0. sauto lq: on use:context_derivative_det.
- sinvert H0. sauto lq: on use:context_derivative_det.
- sinvert H1. sinvert H6. destruct (ltac:(best use:context_derivative_det) : G' = g1'). sfirstorder.
- sinvert H1. sinvert H6. destruct (ltac:(best use:context_derivative_det) : G' = g1'). sfirstorder.
- sinvert H1. sinvert H4. destruct (ltac:(best use:context_derivative_det) : D' = g1'). sfirstorder.
Qed.

Theorem subcontext_ctxsubst : forall G G' G0 x y,
  WFContext G ->
  Subcontext G G' ->
  CtxSubst x y G G0 ->
  (exists G'0, CtxSubst x y G' G'0 /\ Subcontext G0 G'0) \/ (Subcontext G0 G' /\ ~fv G' y).
intros.
  generalize dependent G0.
  generalize dependent H.
  dependent induction H0; intros.
  - edestruct (ctx_subst_fill_arb g d) as [[G' [A [B C]]] | [d'' [A [B C]]]]. eauto. eauto.
    + edestruct (C d' gd') as [g'd' [U V]]; eauto.
    + edestruct IHSubcontext as [[d'0 [A' B']] | [A' B']]. best use:wf_fill. eauto.
      * edestruct (C d') as [gd'0 [U V]]; eauto. 
      *  right. split. { eapply SubCong. eauto. eauto. eauto. } { intro. eapply B'. assert (H00 : fv g y \/ fv d' y) by sfirstorder use: (fv_fill' g). edestruct H00;[|sfirstorder]. assert (fv d y) by sfirstorder use:ctx_subst_found_fv. assert (~fv g y) by qauto l: on use:wf_fill_reflect'. sfirstorder. }
  - best.
  - sinvert H1. best.
  - sinvert H.
    sinvert H1.
    + left. best.
    + best.
  - sinvert H. sinvert H1.
    + left. best.
    + right. split. best. hauto q: on use:ctx_subst_found_fv.
  - sinvert H; sinvert H1.
    + left. best.
    + right. split. best. hauto q: on use:ctx_subst_found_fv.
  - sinvert H. sinvert H1.
    + right. hauto l: on use:ctx_subst_found_fv.
    + left. sfirstorder.
  - best.
  - best.
  - best.
Qed.

  (* G <= G'
  ->
  G[x/y] <: G'[x/y] *)
