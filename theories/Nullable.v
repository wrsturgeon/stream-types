From LambdaST Require Import
  Context
  Invert
  Prefix
  Types.

Inductive NullableTy : type -> Prop :=
  | NullableTyEps : NullableTy TyEps
  | NullableTyPar : forall s t,
      NullableTy s ->
      NullableTy t ->
      NullableTy (TyPar s t)
  .

Inductive NullableCtx : context -> Prop :=
  | NullableCtxEmpty : NullableCtx CtxEmpty
  | NullableCtxComma : forall G G',
      NullableCtx G ->
      NullableCtx G' ->
      NullableCtx (CtxComma G G')
  .

(* Theorem B.19 *)
Theorem nullable_prefix_emp : forall p s,
  PfxTyped p s ->
  NullableTy s ->
  p = emp s.
Proof.
  intros p s Ht Hn. generalize dependent p. induction Hn; intros; simpl in *; invert Ht.
  - reflexivity.
  - apply IHHn1 in H2. apply IHHn2 in H3. subst. reflexivity.
Qed.
