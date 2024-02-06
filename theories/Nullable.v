From LambdaST Require Import
  Context
  Prefix
  Types.

(* Definition B.1 *)
Inductive Nullable : type -> Prop :=
  | NullableTyEps : Nullable TyEps
  | NullableTyPar : forall s t,
      Nullable s ->
      Nullable t ->
      Nullable (TyPar s t)
  .
Arguments Nullable t.
Hint Constructors Nullable : core.

Definition B1 := Nullable.
Arguments B1/ t.

Inductive NullableCtx : context -> Prop :=
  | NullableCtxEmpty : NullableCtx CtxEmpty
  | NullableCtxComma : forall G G',
      NullableCtx G ->
      NullableCtx G' ->
      NullableCtx (CtxComma G G')
  .
Hint Constructors NullableCtx : core.
