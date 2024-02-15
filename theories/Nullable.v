Require Import Coq.Program.Equality.
From LambdaST Require Import
  Context
  Prefix
  Types.
From Hammer Require Import Tactics.

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
  | NullableCtxSng : forall x s, Nullable s -> NullableCtx (CtxHasTy x s)
  | NullableCtxComma : forall G G',
      NullableCtx G ->
      NullableCtx G' ->
      NullableCtx (CtxComma G G')
  .
Hint Constructors NullableCtx : core.

Theorem empty_and_maximal_means_nullable : forall p s,
  EmptyPrefix p ->
  MaximalPrefix p ->
  PrefixTyped p s ->
  Nullable s.
Proof.
  intros p s He Hm Ht.
  dependent induction Ht; sauto lq: on.
Qed.