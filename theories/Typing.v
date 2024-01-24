From LambdaST Require Import
  Context
  Terms
  Types
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
      fill G (CtxComma (CtxHasTy x s) (CtxHasTy y r)) |- e \in r ->
      fill G (CtxHasTy z (TyPar s t)) |- (TmLetPar x y z e) \in r
  | T_Cat_R : forall G D e1 e2 s t,
      G |- e1 \in s ->
      D |- e2 \in t ->
      (CtxSemic G D) |- (e1; e2) \in (TyDot s t)
  | T_Cat_L : forall G x y z s t e r,
      fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y r)) |- e \in r ->
      fill G (CtxHasTy z (TyPar s t)) |- (TmLetCat t x y z e) \in r
  | T_Eps_R : forall G,
      G |- sink \in eps
  | T_One_R : forall G,
      G |- unit \in 1
  | T_Var : forall G x s,
      fill G (CtxHasTy x s) |- (TmVar x) \in s
  | T_SubCtx : forall G G' e s,
      (* Contains G' G -> *)
      G' |- e \in s ->
      G |- e \in s
  | T_Let : forall G D x e e' s t,
      D |- e \in s ->
      fill G (CtxHasTy x s) |- e' \in t ->
      fill G D |- TmLet x e e' \in t
where "G '|-' x '\in' T" := (Typed G x T).

Theorem typing_fv : forall G e s,
    G |- e \in s ->
    forall x, In x (fv e) -> In x (vars_in G).
Admitted.