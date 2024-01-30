From LambdaST Require Import
  Context
  FV
  Hole
  Terms
  Types.

Declare Scope typing_scope.

Reserved Notation "G '|-' x '\in' T" (at level 97).

Inductive Typed : context -> term -> type -> Prop :=
  | TParR : forall G e1 e2 s t,
      G |- e1 \in s ->
      G |- e2 \in t ->
      G |- (e1, e2) \in TyPar s t
  | T_Par_L : forall G x y z s t e r Gxsyt Gzst,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      (*
      fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) |- e \in r ->
      fill G (CtxHasTy z (TyPar s t)) |- (TmLetPar x y z e) \in r
      *)
      FillWith (CtxComma (CtxHasTy x s) (CtxHasTy y t)) G Gxsyt ->
      FillWith (CtxHasTy z (TyPar s t)) G Gzst ->
      Gxsyt |- e \in r ->
      Gzst |- TmLetPar x y z e \in r
  | TCatR : forall G D e1 e2 s t,
      G |- e1 \in s ->
      D |- e2 \in t ->
      CtxSemic G D |- (e1; e2) \in TyDot s t
  | T_Cat_L : forall G x y z s t e r Gxsyt Gzst,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      (*
      fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) |- e \in r ->
      fill G (CtxHasTy z (TyDot s t)) |- (TmLetCat t x y z e) \in r
      *)
      FillWith (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) G Gxsyt ->
      FillWith (CtxHasTy z (TyDot s t)) G Gzst ->
      Gxsyt |- e \in r ->
      Gzst |- TmLetCat t x y z e \in r
  | TEpsR : forall G,
      G |- sink \in eps
  | TOneR : forall G,
      G |- unit \in 1
  | TVar : forall G x s Gxs,
      (* fill G (CtxHasTy x s) |- (TmVar x) \in s *)
      FillWith (CtxHasTy x s) G Gxs ->
      Gxs |- TmVar x \in s
  | TSubCtx : forall G G' e s,
      CtxLEq G G' ->
      G' |- e \in s ->
      G |- e \in s
  | T_Let : forall G D x e e' s t Gxs GD,
      ~fv G x ->
      D |- e \in s ->
      (*
      fill G (CtxHasTy x s) |- e' \in t ->
      fill G D |- TmLet x e e' \in t
      *)
      FillWith (CtxHasTy x s) G Gxs ->
      FillWith D G GD ->
      Gxs |- e' \in t ->
      GD |- TmLet x e e' \in t
  | T_Drop : forall G x s t e Ge Gxs,
      (*
      fill G CtxEmpty |- e \in t ->
      fill G (CtxHasTy x s) |- TmDrop x e \in t
      *)
      FillWith CtxEmpty G Ge ->
      FillWith (CtxHasTy x s) G Gxs ->
      Ge |- e \in t ->
      Gxs |- drop x; e \in t
where "G '|-' x '\in' T" := (Typed G x T).
Hint Constructors Typed : core.

(* TODO:
Theorem typed_wf_term : forall G x T,
  G |- x \in T ->
  WFTerm (fv G) x.
*)
