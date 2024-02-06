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

(*
Theorem soundout : forall G,
  WFContext G ->
  forall e s,
  Typed G e s ->
  forall n,
  EnvTyped n G ->
  forall e' p,
  Step n e e' p -> (
    PrefixTyped p s /\ (
      MaximalOn (fv e) n ->
      MaximalPrefix p)).
Proof.
  intros G Hw e s Ht n He e' p Hs. generalize dependent G. generalize dependent s.
  Print Step. induction Hs; intros.
  - (* S-Var *)
    remember (TmVar x) as vx eqn:Evx. generalize dependent n. generalize dependent x.
    generalize dependent p. generalize dependent Hw. induction Ht; intros; sinvert Evx.
    + destruct (maps_to_has_type _ _ _ _ _ H He) as [p' [Hp1 Hp2]].
      rewrite H0 in Hp1. symmetry in Hp1. sinvert Hp1. split. { assumption. }
      eapply maximal_semantics_aux. constructor. assumption.
    + sinvert H1. eapply IHHt; clear IHHt;
      [eapply sub_preserves_wf | reflexivity | | eapply sub_preserves_env]; eassumption.
  - (* S-Par-R *)
    remember (TmComma e1 e2) as e1e2 eqn:Ee1e2. generalize dependent n. generalize dependent e1.
    generalize dependent e1'. generalize dependent e2. generalize dependent e2'.
    generalize dependent p1. generalize dependent p2. generalize dependent Hw.
    induction Ht; intros; sinvert Ee1e2.
    + specialize (IHHs1 _ _ Hw Ht1 He) as [IH1p IH1m].
      specialize (IHHs2 _ _ Hw Ht2 He) as [IH2p IH2m].
      split. { constructor; assumption. } intro Hm. constructor; [apply IH1m | apply IH2m];
      intros x Hx; apply Hm; [left | right]; assumption.
    + sinvert H0. eassert (Hw' := sub_preserves_wf _ _ H Hw). specialize (IHHt Hw').
      specialize (IHHt _ _ _ _ _ _ eq_refl _ Hs1 Hs2 IHHs1 IHHs2).
      destruct (sub_preserves_env _ _ _ He H) as [He' Ha]. specialize (IHHt He') as [IHp IHm].
      split; assumption.
  - (* S-Par-L *)
    remember (TmLetPar x y z e) as xyze eqn:Exyze. generalize dependent n. generalize dependent x.
    generalize dependent y. generalize dependent z. generalize dependent e. generalize dependent e'.
    generalize dependent p1. generalize dependent p2. generalize dependent p'. generalize dependent Hw.
    induction Ht; intros; sinvert Exyze.
    + assert (HwG := wf_ctx_hole _ Hw _ _ H3). assert (HwGxsyt : WFContext Gxsyt). {
        clear IHHt IHHs. eapply wf_hole_iff. { eassumption. } split. { assumption. }
        split. { repeat constructor; congruence. } split; intros Hx C; [destruct C | destruct Hx]; congruence. }
      specialize (IHHt HwGxsyt). destruct (maps_to_has_type _ _ _ _ _ H3 He) as [p [Hp1 Hp2]].
      rewrite H4 in Hp1. sinvert Hp1. sinvert Hp2. Search e0.
      assert (A : exists x y z e, e0 = TmLetPar x y z e) by admit.
      destruct A as [x' [y' [z' [e'' Exyze]]]]. clear IHHt Hs IHHs. specialize (IHHt _ _ _ _ _ _ _ _ Exyze _ H4).
      Search e0.
      best use: maximal_semantics, maximal_semantics_aux.
      split. { Search p'. clear IHHt Hs IHHs. best. Search e0.
  - (* S-Cat-R-1 *)
  - (* S-Cat-R-2 *)
  - (* S-Cat-L-1 *)
  - (* S-Cat-L-2 *)
  - (* S-Eps-R *)
  - (* S-One-R *)
Qed.
*)

Theorem soundness : forall G,
  WFContext G ->
  forall e s,
  Typed G e s ->
  forall n,
  EnvTyped n G ->
  forall e' p,
  Step n e e' p -> (
    PrefixTyped p s /\ (
      MaximalOn (fv e) n ->
      MaximalPrefix p)).
Proof.
  cbn. intros G Hw e s Ht n He e' p Hs.
  generalize dependent n. generalize dependent e'.
  generalize dependent p. generalize dependent Hw.
  induction Ht; intros. 9: { (* Subtyping/subcontext case first *)
    rename G' into D. (* to match the appendix *)
    destruct (sub_preserves_env _ _ _ He H) as [HD Ha].
    eapply IHHt; [eapply sub_preserves_wf | |]; eassumption. }
  - (* T-Par-R (case 4): (e1, e2) *)
    sinvert Hs. (* now we have the same assumptions as the appendix *)
    specialize (IHHt1 Hw _ _ _ He H2) as [IHa1 IHa2].
    specialize (IHHt2 Hw _ _ _ He H5) as [IHb1 IHb2].
    split. { constructor; assumption. } intros. cbn in *.
    constructor; [apply IHa2 | apply IHb2]; intros; apply H; [left | right]; assumption.
  - (* T-Par-L (case 7): let (x, y) = z in e *)
    sinvert Hs.
    destruct (maps_to_has_type _ _ _ _ _ H3 He) as [nz [Enz Hnz]].
    rewrite H11 in Enz. sinvert Enz. sinvert Hnz.
    assert (HG := wf_ctx_hole _ Hw _ _ H3).
    assert (Hwxsyt : WFContext Gxsyt). {
      eapply wf_hole_iff. { eassumption. } split. { assumption. }
      split; repeat constructor; sfirstorder. }
    specialize (IHHt Hwxsyt). edestruct IHHt as [IHp IHm]; clear IHHt; [admit | eassumption |].
    split. { assumption. } intro Hm. apply IHm; clear IHm. intros test Htest. cbn.
Abort.
(*
    destruct (eqb_spec y test). best use: maximal_semantics, maximal_semantics_aux.
    clear H H0 H1 H2 H3 Ht Hw He H11 H12 H7 H9 HG Hwxsyt IHp Hm.

    clear IHHt H12. eapply env_subctx_bind. Search EnvTyped. fail.
    Print EnvTyped.
    (* TODO: Problem: (EnvTyped _ Gxsyt) is really not necessarily true, not just not provable...
     * Case on whether x & y are bound? Or require something extra a priori?
     * Second problem: even if it were true and provable, the goal doesn't seem provable with it... *)
    shelve.
  - (* T-Cat-R (cases 5-6) *)
    sinvert Hw. sinvert He. sinvert Hs.
    + (* S-Cat-R-1 (case 5) *)
      specialize (IHHt1 H2 _ _ _ H5 H9) as [IH1 IH2]. split. { constructor. assumption. }
      intros. contradiction H12. apply IH2. cbn. intros. apply H0. left. assumption.
    + (* S-Cat-R-2 (case 6) *)
      specialize (IHHt1 H2 _ _ _ H5 H6) as [IH1p IH1i].
      specialize (IHHt2 H3 _ _ _ H7 H13) as [IH2p IH2i].
      split. { constructor; assumption. } intros. constructor; [assumption |].
      apply IH2i. intros x Hfv. apply H0. right. assumption.
  - (* T-Cat-L (cases 8-9) *)
    assert (HG := wf_ctx_hole _ Hw _ _ H3).
    assert (Hw' : WFContext Gxsyt). {
      eapply wf_hole_iff. { eassumption. } split. { assumption. }
      split; repeat constructor; sfirstorder. }
    specialize (IHHt Hw').
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
    assert (HwD : WFContext D). { eapply wf_ctx_plug; eassumption. }
    edestruct IHHt1 as [IH1p IH1i]; clear IHHt1; try eassumption.
    assert (HwG : WFHole G). { eapply wf_ctx_hole; [| eassumption]. congruence. }
    assert (HwGxs : WFContext Gxs). { eapply wf_hole_iff; repeat split; sfirstorder. }
    edestruct IHHt2 as [IH2p IH2i]; clear IHHt2; try eassumption. { shelve. }
    split. { assumption. } intros. eapply maximal_semantics. { eassumption. } { eassumption. }
    cbn. intros test Hfv. destruct (eqb_spec x test). {
      symmetry in e0. subst. eexists. repeat constructor.
      apply IH1i. intros test Htest. apply H2. left. assumption. }
    Abort.
    (*
    best time: 100 use: B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, (* B12, *) B13, B14, B15, B16, B17, B18, B19, B20, B21, B22, B23, B24, B25, B26, (* B27, B28, B29, *) B30, B31, B32, (* B33, *) B34, B35, B36, B37, B38, (* B39 *) B40, (* B41 *) B42, (* B43 *) B44, B45, B46, (* B47 *) B48.
    *)
*)

(*
(* Theorem B.50 *)
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
