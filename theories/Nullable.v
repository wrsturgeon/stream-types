Require Import Coq.Program.Equality.
From LambdaST Require Import
  Context
  Prefix
  Environment
  FV
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
  | NullableCtxSemic : forall G G',
      NullableCtx G ->
      NullableCtx G' ->
      NullableCtx (CtxSemic G G')
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

Theorem emptyon_and_maximalon_means_nullable : forall eta g,
  EmptyOn (fv g) eta ->
  MaximalOn (fv g) eta ->
  EnvTyped eta g ->
  NullableCtx g.
Proof.
  intros eta g He Hm Ht.
  dependent induction Ht.
  - sfirstorder.
  - sauto use:empty_and_maximal_means_nullable.
  - hauto l:on.
  - hauto l:on.
Qed.

Theorem nullable_means_maximal_implies_empty : forall p s,
  Nullable s ->
  PrefixTyped p s ->
  MaximalPrefix p -> EmptyPrefix p.
Proof.
intros p s H Hp.
generalize dependent p.
dependent induction H; sauto lq: on.
Qed.

Theorem nullable_means_empty_implies_maximal : forall p s,
  Nullable s ->
  PrefixTyped p s ->
  EmptyPrefix p -> MaximalPrefix p.
Proof.
intros p s H Hp.
generalize dependent p.
dependent induction H; sauto lq: on.
Qed.

Theorem nullable_context_means_maximalon_implies_emptyon : forall eta g,
  NullableCtx g ->
  EnvTyped eta g ->
  MaximalOn (fv g) eta -> EmptyOn (fv g) eta.
Proof.
intros eta g H Hp.
generalize dependent eta.
dependent induction H.
- sfirstorder.
- sauto use:nullable_means_maximal_implies_empty.
- sauto lq: on rew: off.
- sauto lq: on rew: off.
Qed.

Theorem nullable_context_means_emptyon_implies_maximalon : forall eta g,
  NullableCtx g ->
  EnvTyped eta g ->
  EmptyOn (fv g) eta -> MaximalOn (fv g) eta.
Proof.
intros eta g H Hp.
generalize dependent eta.
dependent induction H.
- sfirstorder.
- sauto use:nullable_means_empty_implies_maximal.
- sauto lq: on rew: off.
- sauto lq: on rew: off.
Qed.