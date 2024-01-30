From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  EnvironmentSubcontextBind
  FV
  Hole
  Prefix
  Sets.

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

Lemma fill_preserves_env : forall (d d' : context) (g : hole) (gd gd' : context),
  FillWith d g gd ->
  FillWith d' g gd' ->
  Subtype d d' ->
  (forall n : env, EnvTyped n d -> EnvTyped n d') ->
  forall n : env,
  EnvTyped n gd ->
  EnvTyped n gd'.
Proof.
  intros d d' g gd gd' Hf Hf' Hs IH n He.
  generalize dependent d. generalize dependent d'. generalize dependent gd. generalize dependent gd'.
  generalize dependent n. induction g; cbn in *; intros;
  sinvert Hf'; sinvert Hf; [apply IH; assumption | | | |]; sinvert He; constructor; try assumption;
  try (eapply IHg; [| eassumption | eassumption | |]; assumption);
  destruct H6; [left; assumption | right | left | right; assumption]. Abort.
(*
  (* TODO: we have to have something to do with `Agree`--maybe Subtype -> Agree? *)
  (eapply prop_on_fill; [eassumption | eassumption | | assumption]).
  admit.
  cbn in *; intros; apply H.

  (eapply prop_on_fill; [| | | eassumption]); eassumption.
Qed.
Hint Resolve fill_preserves_env : core.
*)

(* Theorem B.35 *)
Theorem sub_preserves_env : forall n G D,
  EnvTyped n G ->
  Subtype G D ->
  EnvTyped n D.
Proof.
  intros n G D He Hs. generalize dependent n. induction Hs; cbn in *; intros.
  - shelve. (* eapply fill_preserves_env; [apply H | | | |]; eassumption. *)
  - assumption.
  - sinvert He. constructor; assumption.
  - sinvert He. assumption.
  - sinvert He. assumption.
  - sinvert He. assumption.
  - constructor. { assumption. } constructor.
  - constructor. { assumption. } { constructor. } left. cbn. (* no free variables: holds vacuously *) intros _ [].
  - constructor. { constructor. } { assumption. } right. cbn. (* ditto *) intros _ [].
  Unshelve. Abort.
(*
Qed.
Hint Resolve sub_preserves_env : core.
*)
