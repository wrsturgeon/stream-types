From Coq Require Import
  Program.Wf
  String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  Eqb
  FV
  Hole
  Sets
  Subcontext
  Terms
  Types.

(* TODO: Revise according to B.39 *)
Inductive Typed : context -> term -> type -> Prop :=
  | TParR : forall G e1 e2 s t,
      Typed G e1 s ->
      Typed G e2 t ->
      Typed G (e1, e2) (TyPar s t)
  | TParL : forall G x y z s t e r Gxsyt Gzst,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyPar s t)) Gzst ->
      Typed Gxsyt e r ->
      Typed Gzst (TmLetPar x y z e) r
  | TCatR : forall G D e1 e2 s t,
      Typed G e1 s ->
      Typed D e2 t ->
      DisjointSets (fv G) (fv D) ->
      Typed (CtxSemic G D) (e1; e2) (TyDot s t)
  | TCatL : forall G x y z s t e r Gxsyt Gzst,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyDot s t)) Gzst ->
      Typed Gxsyt e r ->
      Typed Gzst (TmLetCat t x y z e) r
  | TEpsR : forall G,
      Typed G TmSink TyEps
  | TOneR : forall G,
      Typed G TmUnit TyOne
  | TVar : forall G x s Gxs,
      Fill G (CtxHasTy x s) Gxs ->
      Typed Gxs (TmVar x) s
  | TCut : forall G D x e1 e2 s t Gxs GD,
      (* `D` is the context in which we type `e` (as in `let x := e in ...`) *)
      ~fv GD x -> (* <-- TODO: this change (from `G` to `GD`) won't matter theoretically,
                   * but it avoids problematic cases like `let x := x in x`,
                   * where technically the second `x` is not shadowed,
                   * since we carved the first `x` out of the context with its hole *)
      Typed D e1 s ->
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      Typed Gxs e2 t ->
      Typed GD (TmLet s x e1 e2) t
  | TSubCtx : forall G G' e s,
      Subcontext G G' ->
      Typed G' e s ->
      Typed G e s
  .
Arguments Typed G e s.
Hint Constructors Typed : core.

Theorem typing_fv : forall G e s,
  Typed G e s ->
  forall x,
  fv e x ->
  fv G x.
Proof.
  intros G e s Ht x Hfv. generalize dependent x. (* just for naming *)
  induction Ht; try rename x into x' (* hands off my `x`! *); intros x H'; cbn in *.
  - destruct H'; [apply IHHt1 | apply IHHt2]; assumption.
  - eapply fv_fill. { eassumption. } cbn. destruct H' as [| [[H2' H3'] H4]]; [left | right]. { assumption. }
    specialize (IHHt _ H2'). eapply fv_fill in IHHt; [| eassumption].
    cbn in IHHt. destruct IHHt; [| assumption]. destruct H5; contradiction H5.
  - destruct H'; [left; apply IHHt1 | right; apply IHHt2]; assumption.
  - eapply fv_fill. { eassumption. } cbn. destruct H' as [| [[H2' H3'] H4]]; [left | right]. { assumption. }
    specialize (IHHt _ H2'). eapply fv_fill in IHHt; [| eassumption].
    cbn in IHHt. destruct IHHt; [| assumption]. destruct H5; contradiction H5.
  - destruct H' as [].
  - destruct H' as [].
  - eapply fv_fill. { eassumption. } cbn. left. assumption.
  - eapply fv_fill. { eassumption. } cbn. destruct H' as [H' | [H' H'']]; [left | right]. { apply IHHt1. assumption. }
    specialize (IHHt2 _ H'). eapply fv_fill in IHHt2; [| eassumption].
    cbn in IHHt2. destruct IHHt2. { contradiction. } assumption.
  - eapply subctx_fv_subset; [| apply IHHt]; eassumption.
Qed.
Hint Resolve typing_fv : core.

Theorem fv_hole_minus : forall GD,
  WFContext GD ->
  forall G D,
  Fill G D GD ->
  SetEq (fv G) (set_minus (fv GD) (fv D)).
Proof.
  intros GD Hw G D Hf. generalize dependent GD. generalize dependent D.
  induction G; cbn in *; intros.
  - sinvert Hf. split; tauto.
  - sinvert Hf. sinvert Hw. eassert (A := IHG _ _ H1 H3). split; intros.
    2: { repeat destruct H. { right. apply A. split; assumption. } left. assumption. }
    split. { destruct H. { right. assumption. } apply A in H as [H _]. left. assumption. }
    intro C. destruct H; [| apply A in H; tauto].
    assert (H0 := H1). eapply wf_hole_iff in H0 as [Hh [HD Hd]]; [| eassumption].
    apply fv_fill in H3. apply H4 in H. apply H. apply H3. left. assumption.
  - sinvert Hf. sinvert Hw. eassert (A := IHG _ _ H2 H3). split; intros.
    2: { repeat destruct H. { left. assumption. } right. apply A. split; assumption. }
    split. { destruct H. { left. assumption. } apply A in H as [H _]. right. assumption. }
    intro C. destruct H; [| apply A in H; tauto].
    apply fv_fill in H3. apply H4 in H; [destruct H |]. apply H3. left. assumption.
  - sinvert Hf. sinvert Hw. eassert (A := IHG _ _ H1 H3). split; intros.
    2: { repeat destruct H. { right. apply A. split; assumption. } left. assumption. }
    split. { destruct H. { right. assumption. } apply A in H as [H _]. left. assumption. }
    intro C. destruct H; [| apply A in H; tauto].
    assert (H0 := H1). eapply wf_hole_iff in H0 as [Hh [HD Hd]]; [| eassumption].
    apply fv_fill in H3. apply H4 in H. apply H. apply H3. left. assumption.
  - sinvert Hf. sinvert Hw. eassert (A := IHG _ _ H2 H3). split; intros.
    2: { repeat destruct H. { left. assumption. } right. apply A. split; assumption. }
    split. { destruct H. { left. assumption. } apply A in H as [H _]. right. assumption. }
    intro C. destruct H; [| apply A in H; tauto].
    apply fv_fill in H3. apply H4 in H; [destruct H |]. apply H3. left. assumption.
Qed.
Hint Resolve fv_hole_minus : core.

Theorem typed_deeper : forall GD,
  WFContext GD ->
  forall e s,
  Typed GD e s ->
  forall G D,
  Fill G D GD ->
  (forall x, fv e x -> fv D x) ->
  Typed D e s.
Proof.
  (*
  intros GD Hw e s Ht G D HD Hf. generalize dependent Hw. generalize dependent G. generalize dependent D.
  induction Ht; cbn in *; intros.
  - constructor; [eapply IHHt1 | eapply IHHt2]; try eassumption; intros x Hx; apply Hf; [left | right]; assumption.
  - econstructor; [assumption | admit | admit | | |]. econstructor; [assumption | eassumption | assumption | eassumption | | assumption].
  *)

  intros GD Hw e s Ht G D HD Hf. generalize dependent GD. generalize dependent e.
  generalize dependent s. generalize dependent D. induction G; cbn in *; intros; sinvert HD. { assumption. }
  - sinvert Hw. eapply IHG; [assumption | | | eassumption]; [assumption |]; clear IHG.
    remember (CtxComma lhs' g) as ctx eqn:E. generalize dependent G. generalize dependent g.
    generalize dependent D. generalize dependent lhs'. induction Ht; cbn in *; intros; sinvert E.
    + sinvert H. constructor; [eapply IHHt1 | eapply IHHt2]; clear IHHt1 IHHt2; try reflexivity; try eassumption;
      intros x Hx; apply Hf; [left | right]; assumption.
    + sinvert H8. sinvert H3.
      * sinvert H2. cbn in H0. cbn in H1. apply Decidable.not_or in H0. apply Decidable.not_or in H1.
        econstructor; [assumption | | | eassumption | assumption | shelve];
        intro C; [apply H0 in C as [] | apply H1 in C as []].
        Unshelve. eassert (A := H4). eapply wf_hole_iff in A as [Hh [_ Hd]]; [| eassumption].
        eapply IHHt; [| | reflexivity | | |]; clear IHHt. {
          eapply wf_hole_iff; [eassumption |]. split. { eapply wf_ctx_hole. { apply H4. } eassumption. }
          split. { constructor; [constructor | constructor |]. split; congruence. } split; sfirstorder. }
        2: assumption. 2: {
          intro test. apply fv_fill in H12. split; intros Htest C. {
            apply H12 in Htest. cbn in Htest. destruct Htest. { destruct H2; subst; tauto. }
            cbn in *. apply fv_fill in H11. apply H6 in C. apply C. apply H11. right. assumption. }
          apply fv_fill in H7. apply fv_fill in H11. assert (A := typing_fv _ _ _ Ht). apply H12 in C.
          destruct C. { cbn in H2. destruct H2; subst; [apply H0 in Htest as [] | apply H1 in Htest as []]. }
          apply H6 in Htest. apply Htest. apply H11. right. assumption. }
        (* TODO: if this doesn't work, everything above is still perfect, so cut below this line *)
        2: apply FillHere. (* <-- TODO: contentious *)
        intros test Htest. cbn in *. assert (A := typing_fv _ _ _ Ht).
        apply fv_fill in H7. apply fv_fill in H11. apply fv_fill in H12. Abort.
(*
        best time: 100.
        eapply typing_fv; eassumption.
        best.

        { Search e. Search lhs'0. best.
      * clear IHHt.

      ; (econstructor ; [assumption | | | | |]); clear IHHt. admit. admit. admit. admit. admit. admit. admit. admit. eassumption.

    eapply IHG; [| | eassumption |].
    + intros x Hx. eapply fv_fill; [eassumption |]. left. apply Hf. assumption.
    + shelve.
    + eassumption.
    +

  intros Gmax e s Ht. induction Ht; cbn in *; intros.
  - constructor; [apply IHHt1 | apply IHHt2]; try assumption;
    intros; (apply H0; [| assumption]); [left | right]; assumption.
  - econstructor; [assumption | eassumption | assumption | eassumption | | assumption].
    assert (A : ctx_lookup Gzst z = Some (TyPar s t)). { apply ctx_lookup_fill; [| eexists]; eassumption. }
    assert (Hw' := H4). eapply wf_hole_iff in Hw' as [Hh [Hzst Hd]]; [| eassumption].
    assert (B := H5 _ (or_introl eq_refl) _ A). Search ctx_lookup.
    apply ctx_lookup_fill in B; [| eapply wf_hole_iff]. admit. clear IHHt H5 H6. ; [| assumption].
    Search ctx_lookup.
    apply ctx_lookup_fill.
Qed.
*)

Fixpoint typecheck (G : context) (e : term) (s : type) : bool :=
  match e with
    (* T-Eps-R *)
  | TmSink =>
      match s with TyEps => true | _ => false end
    (* T-One-R *)
  | TmUnit =>
      match s with TyOne => true | _ => false end
    (* T-Var *)
  | TmVar x =>
      match ctx_lookup G x with Some t => if eqb s t then true else false | None => false end
    (* T-Par-R *)
  | TmComma e1 e2 =>
      match s with TyPar s t => (typecheck G e1 s && typecheck G e2 t)%bool | _ => false end
    (* T-Cat-R *)
  | TmSemic e1 e2 =>
      match G, s with
      | CtxSemic G' D', TyDot s t => (typecheck G' e1 s && typecheck D' e2 t && ctx_disj G' D')%bool
      | _, _ => false
      end
    (* T-Cut *)
  | TmLet t x e1 e2 =>
      let fve1 := fv_term_li e1 in
      let GD := G in
      let (G, D) := zoom_in fve1 G in (
        (negb (lcontains x (fv_ctx_li GD))) &&
        typecheck D e1 t &&
        typecheck (fill G (CtxHasTy x t)) e2 s)%bool
  | TmLetPar x y z e =>
      match poke G z with
      | Some (pair (TyPar tx ty) G) =>
          let fvG := fv_hole_li G in (
            (negb (eqb x y)) &&
            (negb (lcontains x fvG)) &&
            (negb (lcontains y fvG)) &&
            typecheck (fill G (CtxComma (CtxHasTy x tx) (CtxHasTy y ty))) e s)%bool
      | _ => false
      end
  | TmLetCat t x y z e =>
      match poke G z with
      | Some (pair (TyDot tx ty) G) => (
          eqb ty t &&
          let fvG := fv_hole_li G in (
            (negb (eqb x y)) &&
            (negb (lcontains x fvG)) &&
            (negb (lcontains y fvG)) &&
            typecheck (fill G (CtxSemic (CtxHasTy x tx) (CtxHasTy y ty))) e s))%bool
      | _ => false
      end
  end.

Theorem typecheck_not_wrong : forall G,
  WFContext G ->
  forall e s,
  typecheck G e s = true ->
  Typed G e s.
Proof.
  intros G Hw e. generalize dependent G. induction e; cbn in *; intros.
  - destruct s; sinvert H. constructor.
  - destruct s; sinvert H. constructor.
  - destruct (ctx_lookup G id) eqn:E; [| discriminate H].
    apply ctx_lookup_fill in E as [G' EG']; [| assumption].
    destruct (eqb_spec_type s t); sinvert H. econstructor. eassumption.
  - destruct s; try discriminate H. apply Bool.andb_true_iff in H as [H1 H2].
    apply IHe1 in H1; [| assumption]. apply IHe2 in H2; [| assumption]. constructor; assumption.
  - destruct G; try discriminate H. destruct s; try discriminate H. sinvert Hw.
    apply Bool.andb_true_iff in H as [H1 Hd]. apply Bool.andb_true_iff in H1 as [Ht1 Ht2].
    apply IHe1 in Ht1; [| assumption]. apply IHe2 in Ht2; [| assumption]. constructor; assumption.
  - assert (Hf := zoom_in_full G (fv_term_li e1)). destruct (zoom_in (fv_term_li e1) G) as [G' D'] eqn:E.
    apply Bool.andb_true_iff in H as [H1 H2]. apply Bool.andb_true_iff in H1 as [Hb H1].
    destruct (reflect_fv_ctx G bind); sinvert Hb.
    assert (A := Hw). apply (wf_hole_iff _ _ _ Hf) in A as [HG' [HD' Hd]].
    assert (T1 := IHe1 _ HD' _ H1). eassert (Hw' : WFContext (fill G' (CtxHasTy bind t))). {
      eapply wf_hole_iff. { apply reflect_fill. reflexivity. } split; [assumption |]. split; [constructor |].
      assert (A := fv_fill _ _ _ Hf). split; [intros H -> | intros -> H]; apply n; apply A; right; assumption. }
    assert (T2 := IHe2 _ Hw' _ H2). econstructor; [assumption | eassumption | | eassumption | eassumption].
    apply reflect_fill. reflexivity.
  - destruct (poke G bound) as [[h z] |] eqn:Ep; [| discriminate H].
    destruct h; try discriminate H. repeat apply Bool.andb_true_iff in H as [H].
    destruct (String.eqb_spec lhs rhs); sinvert H.
    destruct (reflect_fv_hole z lhs); sinvert H2.
    destruct (reflect_fv_hole z rhs); sinvert H1.
    assert (Hf := poke_fill _ _ _ _ Ep). econstructor; try eassumption. { apply reflect_fill. reflexivity. }
    apply IHe; [| assumption]. eapply wf_hole_iff. { apply reflect_fill. reflexivity. }
    split. { eapply wf_ctx_hole; eassumption. } split. { repeat constructor; congruence. } split; hauto q: on.
  - destruct (poke G bound) as [[h z] |] eqn:Ep; [| discriminate H]. destruct h; try discriminate H.
    apply Bool.andb_true_iff in H as [He H]. apply Bool.andb_true_iff in H as [H Ht].
    apply Bool.andb_true_iff in H as [H Hr]. apply Bool.andb_true_iff in H as [Hn Hl].
    destruct (String.eqb_spec lhs rhs); sinvert Hn.
    destruct (reflect_fv_hole z lhs); sinvert Hl.
    destruct (reflect_fv_hole z rhs); sinvert Hr.
    destruct (eqb_spec_type h2 t); sinvert He.
    assert (Hf := poke_fill _ _ _ _ Ep). econstructor; try eassumption. { apply reflect_fill. reflexivity. }
    apply IHe; [| assumption]. eapply wf_hole_iff. { apply reflect_fill. reflexivity. }
    split. { eapply wf_ctx_hole; eassumption. } split. { repeat constructor; congruence. } split; hauto q: on.
Qed.

Theorem typecheck_complete : forall G,
  WFContext G ->
  forall e s,
  Typed G e s ->
  typecheck G e s = true.
Proof.
  intros G Hw e s Ht. generalize dependent Hw. induction Ht; intros.
  - cbn. rewrite IHHt1; [rewrite IHHt2 |]; [reflexivity | |]; assumption.
  - cbn. assert (A := Hw). apply (wf_hole_iff _ _ _ H3) in A as [Hh [Hz Hd]].
    assert (A : poke Gzst z = Some (pair (TyPar s t) G)); [| rewrite A; clear A]. {
      apply fill_poke. { apply Hd. reflexivity. } assumption. }
    repeat (apply Bool.andb_true_iff; split).
    + apply eqb_neq in H. rewrite H. reflexivity.
    + destruct (reflect_fv_hole G x); tauto.
    + destruct (reflect_fv_hole G y); tauto.
    + assert (E := H2). apply reflect_fill in E. rewrite <- E. clear E.
      apply IHHt. eapply wf_hole_iff. { eassumption. } split. { assumption. }
      split. { constructor; [constructor | constructor |]. intro test. split; congruence. }
      intro test. split; intros Hfv C. destruct C; congruence. destruct Hfv; congruence.
  - sinvert Hw. cbn. rewrite IHHt1; [| assumption]. rewrite IHHt2; [| assumption].
    apply (Bool.reflect_iff _ _ (reflect_ctx_disj _ _)) in H4. rewrite H4. reflexivity.
  - cbn. assert (A := Hw). apply (wf_hole_iff _ _ _ H3) in A as [Hh [Hz Hd]].
    assert (A : poke Gzst z = Some (pair (TyDot s t) G)); [| rewrite A; clear A]. {
      apply fill_poke. { apply Hd. reflexivity. } assumption. }
    repeat (apply Bool.andb_true_iff; split).
    + destruct (eqb_spec_type t t); [| contradiction n]; reflexivity.
    + apply eqb_neq in H. rewrite H. reflexivity.
    + destruct (reflect_fv_hole G x); tauto.
    + destruct (reflect_fv_hole G y); tauto.
    + assert (E := H2). apply reflect_fill in E. rewrite <- E. clear E.
      apply IHHt. eapply wf_hole_iff. { eassumption. } split. { assumption. }
      split. { constructor; [constructor | constructor |]. intro test. split; congruence. }
      intro test. split; intros Hfv C. destruct C; congruence. destruct Hfv; congruence.
  - reflexivity.
  - reflexivity.
  - cbn. assert (E : ctx_lookup Gxs x = Some s). { apply ctx_lookup_fill. { assumption. } eexists. eassumption. }
    rewrite E. destruct (eqb_spec_type s s); [| contradiction n]; reflexivity.
  - (* Cut/let case. Problem here is that the hole could be in arbitrarily many places and still typecheck.
     * I believe the trick will be showing that if the hole were any smaller, you couldn't type `e1`,
     * and if the hole were any larger, you might lose variables in the body.
     * Let's try induction on the hole in the typing derivation... *)
    cbn. destruct (zoom_in (fv_term_li e1) GD) as [G0 D0] eqn:E.
    generalize dependent D. generalize dependent x. generalize dependent e1. generalize dependent e2.
    generalize dependent s. generalize dependent t. generalize dependent Gxs. generalize dependent GD.
    generalize dependent G0. generalize dependent D0. induction G; cbn in *; intros.
    + sinvert H0. sinvert H1. repeat (apply Bool.andb_true_iff; split).
      * destruct (reflect_fv_ctx GD x); [| reflexivity]. contradiction H.
      * Abort.
(*
    cbn. destruct (zoom_in (fv_term_li e1) GD) as [G0 D0] eqn:E. repeat (apply Bool.andb_true_iff; split).
    + destruct (reflect_fv_ctx GD x); [| reflexivity]. contradiction H.
    + admit.
    + admit.
  - generalize dependent e. generalize dependent s. generalize dependent Hw. induction H; cbn in *; intros.
    + apply IHHt. assumption.
    + sinvert Hw. best.
Qed.
*)

Theorem typecheck_correct : forall G,
  WFContext G ->
  forall e s,
  Bool.reflect (Typed G e s) (typecheck G e s).
Proof. (* TODO: best use: typecheck_not_wrong, typecheck_complete *) Abort.

(* TODO: add WF weakening theorem assuming all FVs are covered, then use the above to prove the below *)

(*
Theorem typed_wf_term : forall G x T,
  Typed G x T ->
  WFTerm (fv G) x.
Proof.
  intros. induction H; intros.
  - (* (e1, e2) *)
    constructor; assumption.
  - (* let (x, y) = z in e *)
    shelve. (* until `inert` (might change something) *)
    (*
    constructor; cbn in *.
    + assert (Fxsyt := fv_fill _ _ _ H2). assert (Fzst := fv_fill _ _ _ H3). cbn in *.
      eapply wf_set_eq; [| eassumption]. cbn. intro test. rewrite Fzst. rewrite Fxsyt. split; intros H'.
      * destruct H' as [H' | H']. { right. assumption. } left. split. { right. assumption. } intro. subst. Search test. best use: fv_fill time: 10.
        destruct H' as [H' | H']; subst. { right. left. reflexivity. } right. right. best.
    *)
  - (* (e1; e2) *)
    cbn in *. constructor. eapply typing_fv in H. Abort. (* TODO *)
*)
