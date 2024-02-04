From Coq Require Import String.
From Coq.Relations Require Import Relation_Operators.
From Coq.Wellfounded Require Import Lexicographic_Product.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Derivative
  EnvConcat
  Environment
  FV
  Hole
  Inert
  MaximalSemantics
  Prefix
  Semantics
  Sets
  Subcontext
  Terms
  Types
  Typing.

Theorem soundout : forall G e s,
  Typed G e s ->
  forall n e' p,
  Step n e e' p ->
  WFContext G ->
  EnvTyped n G -> (
    PrefixTyped p s /\ (
      MaximalOn (fv e) n ->
      MaximalPrefix p)).
Proof.
  intros G e s Ht n e' p Hs Hwf He.
  generalize dependent n. generalize dependent e'.
  generalize dependent p. generalize dependent Hwf.
  induction Ht; intros. 8: { (* Subtyping/subcontext case first *)
    rename G' into D. (* to match the appendix *)
    destruct (sub_preserves_env _ _ _ He H) as [HD Ha].
    eapply IHHt; [eapply sub_preserves_wf | |]; eassumption. }
  - (* T-Par-R (case 4) *)
    sinvert Hs. (* now we have the same assumptions as the appendix *)
    specialize (IHHt1 Hwf _ _ _ H2 He) as [IHa1 IHa2].
    specialize (IHHt2 Hwf _ _ _ H5 He) as [IHb1 IHb2].
    split. { constructor; assumption. } intros. cbn in *.
    constructor; [apply IHa2 | apply IHb2]; intros; apply H; [left | right]; assumption.
  - (* T-Par-L (case 7) *)
    sinvert Hs.
    destruct (maps_to_has_type _ _ _ _ _ H3 He) as [nz [Enz Hnz]].
    rewrite H11 in Enz. sinvert Enz. sinvert Hnz.
    assert (HG := wf_ctx_hole _ Hwf _ _ H3).
    assert (Hwf' : WFContext Gxsyt). {
      eapply wf_hole_iff. { eassumption. } split. { assumption. }
      split; repeat constructor; sfirstorder. }
    specialize (IHHt Hwf' _ _ _ H12) as [Hp Hi]. { shelve. } split. { assumption. } intros.
    eapply maximal_semantics; try eassumption. shelve.
  - (* T-Cat-R (cases 5-6) *)
    sinvert Hwf. sinvert He. sinvert Hs.
    + (* S-Cat-R-1 (case 5) *)
      specialize (IHHt1 H2 _ _ _ H9 H5) as [IH1 IH2]. split. { constructor. assumption. }
      intros. contradiction H12. apply IH2. cbn. intros. apply H0. left. assumption.
    + (* S-Cat-R-2 (case 6) *)
      specialize (IHHt1 H2 _ _ _ H6 H5) as [IH1p IH1i].
      specialize (IHHt2 H3 _ _ _ H13 H7) as [IH2p IH2i].
      split. { constructor; assumption. } intros. constructor; [assumption |].
      apply IH2i. intros x Hfv. apply H0. right. assumption.
  - (* T-Cat-L (cases 8-9) *)
    assert (HG := wf_ctx_hole _ Hwf _ _ H3).
    assert (Hwf' : WFContext Gxsyt). {
      eapply wf_hole_iff. { eassumption. } split. { assumption. }
      split; repeat constructor; sfirstorder. }
    specialize (IHHt Hwf').
    sinvert Hs.
    + (* T-Cat-L-1 (case 8) *)
      destruct (maps_to_has_type _ _ _ _ _ H3 He) as [nz [Enz Hnz]].
      rewrite H12 in Enz. sinvert Enz. sinvert Hnz.
      specialize (IHHt _ _ _ H13) as [Hpr IH]. { shelve. } split. { assumption. } intros.
      destruct (derivative_fun _ _ H6) as [s' Hs'].
      eapply maximal_semantics; try eassumption. shelve.
    + (* T-Cat-L-2 (case 9) *)
      destruct (maps_to_has_type _ _ _ _ _ H3 He) as [nz [Enz Hnz]].
      rewrite H12 in Enz. sinvert Enz. sinvert Hnz.
      specialize (IHHt).
      edestruct (IHHt _ _ _ H13) as [Hpr IH]. { shelve. } split. { assumption. } intros.
      destruct (derivative_fun _ _ H10) as [t' Ht'].
      eapply maximal_semantics; try eassumption; shelve.
  - (* T-Eps-R (case 2) *)
    sinvert Hs. split; constructor.
  - (* T-One-R (case 3) *)
    sinvert Hs. split; constructor.
  - (* T-Var (case 4) *)
    sinvert Hs. destruct (maps_to_has_type _ _ _ _ _ H He) as [nx [Enx Hnx]].
    rewrite H2 in Enx. sinvert Enx. split. { assumption. }
    intros. eapply maximal_semantics_aux; [| eassumption]. constructor. eassumption.
  - (* T-Let / T-Cut (case 22) *)
    sinvert Hs. eassert (HD := maps_to_hole _ _ _ _ H1 He).
    eassert (HwfD := wf_ctx_plug _ Hwf _ _ H1).
    specialize (IHHt1 HwfD _ _ _ H8 HD) as [IH1p IH1i].
    assert (E1 := H1). apply reflect_fill in E1. assert (E2 := H0). apply reflect_fill in E2. subst.
    split. Abort.

(*
(* Theorem B.50 *)
Theorem soundness : forall G e s,
  Typed G e s ->
  forall n e' p,
  Step n e e' p ->
  EnvTyped n G -> (
    PrefixTyped p s /\ forall G' s',
      ContextDerivative n G G' ->
      Derivative p s s' ->
      Typed G' e' s').
Proof.
  intros G e s Ht n e' p Hs He. generalize dependent n. generalize dependent e'.
  generalize dependent p. induction Ht; intros. 8: { (* Subtyping/subcontext case! *)
    rename G' into D. (* to match the appendix *)
    destruct (sub_preserves_env _ _ _ He H) as [HD Ha].
    specialize (IHHt _ _ _ Hs HD) as [IH1 IH2]. split. { assumption. }
    intros G' s' Hc Hd. destruct (context_derivative_fun _ _ HD) as [D' HD'].
    eapply deriv_subctx in H; [econstructor; [| eapply IH2] | |]; eassumption. }
  - (* T-Par-R (case 4) *)
    sinvert Hs. (* now we have the same assumptions as the appendix *)
    specialize (IHHt1 _ _ _ H2 He) as [IHa1 IHa2].
    specialize (IHHt2 _ _ _ H5 He) as [IHb1 IHb2].
    split. { constructor; assumption. } intros G' s' Hc Hd. sinvert Hd.
    constructor; [apply IHa2 | apply IHb2]; assumption.
  - (* T-Par-L (case 7) *)
    sinvert Hs.
    destruct (maps_to_has_type _ _ _ _ _ H3 He) as [nz [Enz Hnz]]. rewrite H11 in Enz. sinvert Enz. sinvert Hnz.
    edestruct (IHHt _ _ _ H12) as [Hp Hi]. { shelve. } split. { assumption. }
    intros G0 r' Hc Hd. eapply TParL; try eassumption; shelve.
  - (* T-Cat-R (cases 5-6) *)
    sinvert He. sinvert Hs.
    + (* S-Cat-R-1 (case 5) *)
      specialize (IHHt1 _ _ _ H6 H2) as [IH1 IH2]. split. { constructor. assumption. }
      intros G0 s0 Hc Hd. sinvert Hc. sinvert Hd. apply TCatR. { apply IH2; assumption. } 2: {
        intro x. specialize (H x). apply ctx_deriv_fv in H7. apply ctx_deriv_fv in H10.
        split; intros C1 C2; [apply H7 in C1; apply H10 in C2 |
          apply H10 in C1; apply H7 in C2]; sfirstorder. }
      destruct H5. 2: { eassert (C := maximal_semantics _ _ _ _ _ _ H6 Ht1 H0). tauto. }
      assert (D' = D). { shelve. } subst. assumption.
    + (* S-Cat-R-2 (case 6) *)
      specialize (IHHt1 _ _ _ H3 H2) as [IH1p IH1i]. specialize (IHHt2 _ _ _ H10 H4) as [IH2p IH2i].
      split. { constructor; eassumption. } intros G0 s0 Hc Hd. sinvert Hc. sinvert Hd.
      econstructor; [| apply IH2i; eassumption]. constructor.
  - (* T-Cat-L (cases 8-9) *)
    sinvert Hs.
    + (* T-Cat-L-1 (case 8) *)
      destruct (maps_to_has_type _ _ _ _ _ H3 He) as [nz [Enz Hnz]].
      rewrite H12 in Enz. sinvert Enz. sinvert Hnz.
      edestruct (IHHt _ _ _ H13) as [Hpr IH]. { shelve. } split. { assumption. }
      intros G0 r' Hc Hd. destruct (derivative_fun _ _ H6) as [s' Hs'].
      econstructor; try eassumption; shelve.
    + (* T-Cat-L-2 (case 9) *)
      destruct (maps_to_has_type _ _ _ _ _ H3 He) as [nz [Enz Hnz]].
      rewrite H12 in Enz. sinvert Enz. sinvert Hnz.
      edestruct (IHHt _ _ _ H13) as [Hpr IH]. { shelve. } split. { assumption. }
      intros G0 r' Hc Hd. destruct (derivative_fun _ _ H10) as [t' Ht'].
      econstructor; try eassumption; shelve.
  - (* T-Eps-R (case 2) *)
    sinvert Hs. split. { constructor. } intros. sinvert H0. constructor.
  - (* T-One-R (case 3) *)
    sinvert Hs. split. { constructor. } intros. sinvert H0. constructor.
  - (* T-Var (case 4) *)
    sinvert Hs. destruct (maps_to_has_type _ _ _ _ _ H He) as [nx [Enx Hnx]].
    rewrite H2 in Enx. sinvert Enx. split. { assumption. } intros. econstructor. shelve.
  - (* T-Let / T-Cut (case 22) *)
    sinvert Hs. eassert (HD := maps_to_hole _ _ _ _ H1 He).
    destruct (IHHt1 _ _ _ H8 HD) as [IH1p IH1i].
    assert (E1 := H1). apply reflect_fill in E1. assert (E2 := H0). apply reflect_fill in E2. subst.
    eassert (A := env_subctx_bind _ _ _ _ _ _ He _ _).
    destruct (IHHt2 _ _ _ H9 A) as [IH2p IH2i]. split. { assumption. } intros G0 t' Hc Hd.
    destruct (env_subctx_bind_deriv _ _ _ H1 _ _ Hc) as [G' HG']. shelve.
  Unshelve. Abort.
*)
