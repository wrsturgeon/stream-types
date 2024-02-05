From Coq Require Import
  Program.Wf
  String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
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
      ~fv G x ->
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
    (* T-Let *)
  | TmLet t x e1 e2 =>
      let fve1 := fv_term_li e1 in
      let (G, D) := zoom_in fve1 G in (
        (negb (lcontains x (fv_hole_li G))) &&
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
    destruct (reflect_fv_hole G' bind); sinvert Hb.
    apply IHe1 in H1; [| eapply wf_ctx_plug; eassumption]. apply IHe2 in H2. 2: {
      eapply wf_hole_iff. { apply reflect_fill. reflexivity. } split. { eapply wf_ctx_hole; eassumption. }
      split. { constructor. } assert (A := fv_fill _ _ _ Hf). split; congruence. }
    econstructor; [eassumption | eassumption | | assumption | eassumption]. apply reflect_fill. reflexivity.
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
  - cbn. destruct (poke Gzst z) as [[zt h] |] eqn:Ep. admit.

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
