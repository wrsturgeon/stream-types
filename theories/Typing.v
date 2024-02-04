From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
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
  | TSubCtx : forall G G' e s,
      Subcontext G G' ->
      Typed G' e s ->
      Typed G e s
  | TLet : forall G D x e e' s t Gxs GD,
      ~fv G x ->
      Typed D e s ->
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      Typed Gxs e' t ->
      Typed GD (TmLet x e e') t
  .
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
  - eapply subctx_fv_subset; [| apply IHHt]; eassumption.
  - eapply fv_fill. { eassumption. } cbn. destruct H' as [H' | [H' H'']]; [left | right]. { apply IHHt1. assumption. }
    specialize (IHHt2 _ H'). eapply fv_fill in IHHt2; [| eassumption].
    cbn in IHHt2. destruct IHHt2. { contradiction. } assumption.
Qed.
Hint Resolve typing_fv : core.

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
