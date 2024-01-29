From LambdaST Require Import
  Context
  Terms
  Types
  FV
  Hole.
From Coq Require Import
  List.

From Hammer Require Import Tactics.

Declare Scope typing_scope.

Reserved Notation "G '|-' x '\in' T" (at level 98).

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
    intros G e s H.
    induction H; intros x0 Hfv; cbn in *.
    - sfirstorder.
    - destruct Hfv; hauto q: on use: fv_fill.
    - sfirstorder.
    - destruct Hfv; hauto q: on use: fv_fill.
    - sfirstorder.
    - sfirstorder.
    - sfirstorder use: fv_fill.
    - sfirstorder.
    - destruct Hfv; hauto q: on use: fv_fill.
    - hauto q: on use:fv_fill.
Qed.
Hint Resolve typing_fv : core.
