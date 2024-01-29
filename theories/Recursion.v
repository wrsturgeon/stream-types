From LambdaST Require Import
  Context
  History
  Hole
  Subtyping
  Terms
  Types.

Definition TODO : Set := True. (* TODO: no clue how `s` should be typed below *)

(* Definition B.37 *)
Variant rec_sig : Set :=
  | RecSigEmpty
  | RecSigRecur (H (* Omega *) : hist_ctx) (G : context) (s : TODO)
  .
(* Notation "H '|' G '->' s" := (RecSigRecur H G s) (at level 97, right associativity). *)
Hint Constructors rec_sig : core.

Inductive RTyped (H : hist_ctx) : context -> term -> type -> Prop :=
  | TEpsR : forall G,
      RTyped H G TmSink TyEps
  | TOneR : forall G,
      RTyped H G TmUnit TyOne
  | TVar : forall G x s Gxs,
      FillWith (CtxHasTy x s) G Gxs ->
      RTyped H Gxs (TmVar x) s
  | TSub : forall G D e s,
      Subtype G D ->
      RTyped H D e s ->
      RTyped H G e s
  | TParR : forall G e1 e2 s t,
      RTyped H G e1 s ->
      RTyped H G e2 t ->
      RTyped H G (TmComma e1 e2) (TyPar s t)
  | TCatR : forall G D e1 e2 s t,
      RTyped H G e1 s ->
      RTyped H D e2 t ->
      RTyped H (CtxSemic G D) (TmSemic e1 e2) (TyDot s t)
  | TParL : forall G x y z s t e r Gxsyt Gzst,
      let xs_yt := CtxComma (CtxHasTy x s) (CtxHasTy y t) in
      FillWith xs_yt G Gxsyt ->
      FillWith (CtxHasTy z (TyPar s t)) G Gzst ->
      RTyped H Gxsyt e r ->
      RTyped H Gzst (TmLetPar x y z e) r
  | TCatL : forall G x y z s t e r Gxsyt Gzst,
      let xs_yt := CtxComma (CtxHasTy x s) (CtxHasTy y t) in
      FillWith xs_yt G Gxsyt ->
      FillWith (CtxHasTy z (TyDot s t)) G Gzst ->
      RTyped H Gxsyt e r ->
      RTyped H Gzst (TmLetCat x y z e) r
  | TPlusR1 : forall G e s t,
      RTyped H G e s ->
      RTyped H G (TmInl e) (TySum s t)
  .
(* Notation "H '|' G '|-E' x ':' t" := (RTyped H G x t) (at level 97, right associativity). *)
Hint Constructors RTyped : core.
