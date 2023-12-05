From LambdaST Require Import
  Context
  Invert
  Prefix
  Types.

Inductive Nullable : type -> Prop :=
  | NullableTyEps : Nullable TyEps
  | NullableTyPar : forall s t,
      Nullable s ->
      Nullable t ->
      Nullable (TyPar s t)
  .

Inductive NullableCtx : context -> Prop :=
  | NullableCtxEmpty : NullableCtx CtxEmpty
  | NullableCtxComma : forall G G',
      NullableCtx G ->
      NullableCtx G' ->
      NullableCtx (CtxComma G G')
  .
