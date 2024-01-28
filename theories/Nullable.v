From LambdaST Require Import
  Context
  Prefix
  Types.

Inductive Nullable : type -> Prop :=
  | NullableTyEps : Nullable TyEps
  | NullableTyPar : forall s t,
      Nullable s ->
      Nullable t ->
      Nullable (TyPar s t)
  .
Hint Constructors Nullable : core.

Inductive NullableCtx : context -> Prop :=
  | NullableCtxEmpty : NullableCtx CtxEmpty
  | NullableCtxComma : forall G G',
      NullableCtx G ->
      NullableCtx G' ->
      NullableCtx (CtxComma G G')
  .
Hint Constructors NullableCtx : core.
