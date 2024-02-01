From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  FV
  Hole
  Sets
  Terms
  Types.

Declare Scope typing_scope.

Reserved Notation "G '|-' x '\in' T" (at level 97).

Inductive Typed : context -> term -> type -> Prop :=
  | TParR : forall G e1 e2 s t,
      G |- e1 \in s ->
      G |- e2 \in t ->
      G |- (e1, e2) \in TyPar s t
  | TParL : forall G x y z s t e r Gxsyt Gzst,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyPar s t)) Gzst ->
      Gxsyt |- e \in r ->
      Gzst |- TmLetPar x y z e \in r
  | TCatR : forall G D e1 e2 s t,
      G |- e1 \in s ->
      D |- e2 \in t ->
      DisjointSets (fv G) (fv D) ->
      CtxSemic G D |- (e1; e2) \in TyDot s t
  | TCatL : forall G x y z s t e r Gxsyt Gzst,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyDot s t)) Gzst ->
      Gxsyt |- e \in r ->
      Gzst |- TmLetCat t x y z e \in r
  | TEpsR : forall G,
      G |- sink \in eps
  | TOneR : forall G,
      G |- unit \in 1
  | TVar : forall G x s Gxs,
      Fill G (CtxHasTy x s) Gxs ->
      Gxs |- TmVar x \in s
  | TSubCtx : forall G G' e s,
      CtxLEq G G' ->
      G' |- e \in s ->
      G |- e \in s
  | TLet : forall G D x e e' s t Gxs GD,
      ~fv G x ->
      D |- e \in s ->
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      Gxs |- e' \in t ->
      GD |- TmLet x e e' \in t
where "G '|-' x '\in' T" := (Typed G x T).
Hint Constructors Typed : core.

Theorem typed_fv : forall G e s,
  G |- e \in s ->
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
  - cbn in *. specialize (IHHt _ H'). invert H. (* TODO: SubCtx hasn't been defined yet, so holds vacuously *)
  - eapply fv_fill. { eassumption. } cbn. destruct H' as [H' | [H' H'']]; [left | right]. { apply IHHt1. assumption. }
    specialize (IHHt2 _ H'). eapply fv_fill in IHHt2; [| eassumption].
    cbn in IHHt2. destruct IHHt2. { contradiction. } assumption.
Qed.
Hint Resolve typed_fv : core.

(* TODO: add WF weakening theorem assuming all FVs are covered, then use the above to prove the below *)

(*
Theorem typed_wf_term : forall G x T,
  G |- x \in T ->
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
    cbn in *. constructor. eapply typed_fv in H. Abort. (* TODO *)
*)
