From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  Hole.

(* Definition B.34 *)
(* Argument order designed for notation: (Subtype A B) === (A <: B) *)
Inductive Subtype : context -> context -> Prop :=
  | SubCong : forall d d' g gd gd',
      FillWith d g gd ->
      FillWith d' g gd' ->
      Subtype d d' ->
      Subtype gd gd'
  | SubRefl : forall g,
      Subtype g g
  | SubCommaExc : forall g d,
      Subtype (CtxComma g d) (CtxComma d g)
  | SubCommaWkn : forall g d,
      Subtype (CtxComma g d) g
  (* don't need right-hand comma weakening b/c we have exchange *)
  | SubSemicWkn1 : forall g d,
      Subtype (CtxSemic g d) g
  | SubSemicWkn2 : forall g d,
      Subtype (CtxSemic g d) d
  | SubCommaUnit : forall g,
      Subtype g (CtxComma g CtxEmpty)
  | SubSemicUnit1 : forall g,
      Subtype g (CtxSemic g CtxEmpty)
  | SubSemicUnit2 : forall g,
      Subtype g (CtxSemic CtxEmpty g)
  .
Hint Constructors Subtype : core.

Conjecture fill_preserves_env : forall (d d' : context) (g : hole) (gd gd' : context),
  FillWith d g gd ->
  FillWith d' g gd' ->
  Subtype d d' ->
  (forall n : env, EnvTyped n d -> EnvTyped n d') ->
  forall n : env,
  EnvTyped n gd ->
  EnvTyped n gd'.
(*
Proof.
  generalize dependent d. generalize dependent gd. generalize dependent n.
  induction H0; cbn in *; intros; sinvert H.
  - sfirstorder.
  - sinvert He. sfirstorder.
  - sinvert He. constructor; [| eapply IHFillWith]; eassumption.
  - sinvert He. constructor; [sfirstorder | sfirstorder |]. destruct H6. { left. assumption. } right. admit.
  - sinvert He. constructor; [sfirstorder | sfirstorder |]. destruct H6. 2: { right. assumption. } left. admit.
Qed.
*)
Hint Resolve fill_preserves_env : core.

(* Theorem B.35 *)
Theorem sub_preserves_env : forall n G D,
  EnvTyped n G ->
  Subtype G D ->
  EnvTyped n D.
Proof.
  intros n G D He Hs. generalize dependent n. induction Hs; cbn in *; intros.
  - eapply fill_preserves_env; [apply H | | | |]; eassumption.
  - assumption.
  - sinvert He. constructor; assumption.
  - sinvert He. assumption.
  - sinvert He. assumption.
  - sinvert He. assumption.
  - constructor. { assumption. } constructor.
  - constructor. { assumption. } { constructor. } left. cbn. (* no free variables: holds vacuously *) intros _ [].
  - constructor. { constructor. } { assumption. } right. cbn. (* ditto *) intros _ [].
Qed.
Hint Resolve sub_preserves_env : core.
