From LambdaST Require Import
  Context
  FV
  Hole
  Sets
  Terms
  Types.
From Coq Require Import
  List
  String.

From Hammer Require Import Tactics.

Declare Scope typing_scope.

Reserved Notation "G '|-' x '\in' T" (at level 97).

Inductive Typed : context -> term -> type -> Prop :=
  | T_Par_R : forall G e1 e2 s t,
      G |- e1 \in s ->
      G |- e2 \in t ->
      G |- (TmComma e1 e2) \in (TyPar s t)
  | T_Par_L : forall G x y z s t e r,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) |- e \in r ->
      fill G (CtxHasTy z (TyPar s t)) |- (TmLetPar x y z e) \in r
  | T_Cat_R : forall G D e1 e2 s t,
      G |- e1 \in s ->
      D |- e2 \in t ->
      (CtxSemic G D) |- (e1; e2) \in (TyDot s t)
  | T_Cat_L : forall G x y z s t e r,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) |- e \in r ->
      fill G (CtxHasTy z (TyDot s t)) |- (TmLetCat t x y z e) \in r
  | T_Eps_R : forall G,
      G |- sink \in eps
  | T_One_R : forall G,
      G |- unit \in 1
  | T_Var : forall G x s,
      fill G (CtxHasTy x s) |- (TmVar x) \in s
  | T_SubCtx : forall G G' e s,
      SubCtx G G' ->
      G' |- e \in s ->
      G |- e \in s
  | T_Let : forall G D x e e' s t,
      ~(fv G x) ->
      D |- e \in s ->
      fill G (CtxHasTy x s) |- e' \in t ->
      fill G D |- TmLet x e e' \in t
  | T_Drop : forall G x s t e,
      fill G CtxEmpty |- e \in t ->
      fill G (CtxHasTy x s) |- TmDrop x e \in t
where "G '|-' x '\in' T" := (Typed G x T).
Hint Constructors Typed : core.

Theorem typing_fv : forall G e s,
    G |- e \in s ->
    forall x,
    fv e x ->
    fv G x.
Proof.
  intros G e s Ht x Hfv. generalize dependent x. (* just for naming *)
  induction Ht; try rename x into x' (* hands off my `x`! *); intros x H'; cbn in *.
  - destruct H'; [apply IHHt1 | apply IHHt2]; assumption.
  - apply fv_fill_fn. cbn. destruct H' as [| [[H2 H3] H4]]; [left | right]. { assumption. } specialize (IHHt _ H2).
    apply fv_fill_fn in IHHt. cbn in IHHt. destruct IHHt; [| assumption]. destruct H5; contradiction H5.
  - destruct H'; [left; apply IHHt1 | right; apply IHHt2]; assumption.
  - apply fv_fill_fn. cbn. destruct H' as [| [[H2 H3] H4]]; [left | right]. { assumption. } specialize (IHHt _ H2).
    apply fv_fill_fn in IHHt. cbn in IHHt. destruct IHHt; [| assumption]. destruct H5; contradiction H5.
  - destruct H' as [].
  - destruct H' as [].
  - apply fv_fill_fn. cbn. left. assumption.
  - cbn in *. specialize (IHHt _ H'). invert H. (* TODO: SubCtx hasn't been defined yet, so holds vacuously *)
  - apply fv_fill_fn. cbn. destruct H' as [H' | [H' H'']]; [left | right]. { apply IHHt1. assumption. }
    specialize (IHHt2 _ H'). apply fv_fill_fn in IHHt2. cbn in IHHt2. destruct IHHt2. { contradiction. } assumption.
  - apply fv_fill_fn. cbn. destruct H'. specialize (IHHt _ H).
    apply fv_fill_fn in IHHt as [[] | IH]. right. assumption.
Qed.
Hint Resolve typing_fv : core.
