From LambdaST Require Import
  Context
  Terms
  Types.

Declare Scope typing_scope.

Reserved Notation "G '|-' x '\in' T" (at level 98).

Inductive Typed : context -> term -> type -> Prop :=
  | T_Par_R : forall G e1 e2 s t,
      G |- e1 \in s ->
      G |- e2 \in t ->
      G |- (TmComma e1 e2) \in (TyPar s t)
  | T_Par_L : forall Gxy Gz x y z s t e r,
      FindReplace (CtxComma (CtxHasTy x s) (CtxHasTy y t)) (CtxHasTy z (TyPar s t)) Gxy Gz ->
      Gxy |- e \in r ->
      Gz |- (TmLetPar x y z e) \in r
  | T_Cat_R : forall G D e1 e2 s t,
      G |- e1 \in s ->
      D |- e2 \in t ->
      (CtxSemic G D) |- (e1; e2) \in (TyDot s t)
  | T_Cat_L : forall Gxy Gz x y z s t e r,
      FindReplace (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) (CtxHasTy z (TyDot s t)) Gxy Gz ->
      Gxy |- e \in r ->
      Gz |- (TmLetCat x y z e) \in r
  | T_Eps_R : forall G,
      G |- sink \in eps
  | T_One_R : forall G,
      G |- unit \in 1
  | T_Var : forall G x s,
      Contains (CtxHasTy x s) G ->
      G |- (TmVar x) \in s
  | T_SubCtx : forall G G' e s,
      Contains G' G ->
      G' |- e \in s ->
      G |- e \in s
  | T_Let : forall Gxs GD D x e e' s t,
      FindReplace (CtxHasTy x s) D Gxs GD ->
      D |- e \in s ->
      Gxs |- e' \in t ->
      GD |- TmLet x e e' \in t
where "G '|-' x '\in' T" := (Typed G x T).
