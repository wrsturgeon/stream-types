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
  | RecSigRecur (H (* \Omega *) : hist_ctx) (G : context) (s : TODO)
  .
(* Notation "H '|' G '->' s" := (RecSigRecur H G s) (at level 97, right associativity). *)
Hint Constructors rec_sig : core.

Inductive RTyped (H : hist_ctx) : context -> rec_sig -> term -> type -> Prop :=
  | TEpsR : forall G E (* NOTE: `E` for \Sigma *),
      RTyped H G E TmSink TyEps
  | TOneR : forall G E,
      RTyped H G E TmUnit TyOne
  | TVar : forall G E x s Gxs,
      Fill G (CtxHasTy x s) Gxs ->
      RTyped H Gxs E (TmVar x) s
  | TSub : forall G D E e s,
      Subtype G D ->
      RTyped H D E e s ->
      RTyped H G E e s
  | TParR : forall G E e1 e2 s t,
      RTyped H G E e1 s ->
      RTyped H G E e2 t ->
      RTyped H G E (TmComma e1 e2) (TyPar s t)
  | TCatR : forall G D E e1 e2 s t,
      RTyped H G E e1 s ->
      RTyped H D E e2 t ->
      RTyped H (CtxSemic G D) E (TmSemic e1 e2) (TyDot s t)
  | TParL : forall G E x y z s t e r Gxsyt Gzst,
      let xs_yt := CtxComma (CtxHasTy x s) (CtxHasTy y t) in
      Fill G xs_yt Gxsyt ->
      Fill G (CtxHasTy z (TyPar s t)) Gzst ->
      RTyped H Gxsyt E e r ->
      RTyped H Gzst E (TmLetPar x y z e) r
  | TCatL : forall G E x y z s t e r Gxsyt Gzst,
      let xs_yt := CtxComma (CtxHasTy x s) (CtxHasTy y t) in
      Fill G xs_yt Gxsyt ->
      Fill G (CtxHasTy z (TyDot s t)) Gzst ->
      RTyped H Gxsyt E e r ->
      RTyped H Gzst E (TmLetCat t x y z e) r
  | TCut : forall G D E e1 e2 x s t Gxs GD,
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      RTyped H D E e1 s ->
      RTyped H Gxs E e2 t ->
      RTyped H GD E (TmLet x e1 e2) t
      (* TODO: After Full Lambda-ST, implement these:
       * T-Plus-R-1
       * T-Plus-R-2
       * T-Plus-L
       * T-Star-R-1
       * T-Star-R-2
       * T-Star-L
       * T-Wait
       * T-Rec
       * T-Fix *)
      (* TODO: Once B.33 makes sense, implement T-HistPgm *)
  .
Hint Constructors RTyped : core.
