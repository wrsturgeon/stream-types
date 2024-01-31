From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Prefix
  Sets
  Inertness
  .

(* Definition B.34 *)
(* Argument order designed for notation: (Subtype A B) === (A <: B) *)
Inductive Subtype : context -> context -> Prop :=
  | SubCong : forall d d' g gd gd',
      Fill g d gd ->
      Fill g d' gd' ->
      Subtype d d' ->
      Subtype gd gd'
  | SubRefl : forall g,
      Subtype g g
  | SubCommaExc : forall g d,
      Subtype (CtxComma g d) (CtxComma d g)
  | SubCommaUnit : forall g,
      Subtype g (CtxComma g CtxEmpty)
  | SubSemicUnit1 : forall g,
      Subtype g (CtxSemic g CtxEmpty)
  | SubSemicUnit2 : forall g,
      Subtype g (CtxSemic CtxEmpty g)
  .
Hint Constructors Subtype : core.

Lemma fill_preserves_env : forall (d d' : context) (g : hole) (gd gd' : context),
  Fill g d gd ->
  Fill g d' gd' ->
  (* Subtype d d' -> *)
  (forall n : env, EnvTyped n d -> EnvTyped n d') ->
  forall n : env,
  (* NOTE: added the agreement, should be good here. *)
  Agree Inert n n (fv d) (fv d') ->
  EnvTyped n gd ->
  EnvTyped n gd'.
Proof.
  intros d d' g gd gd' Hf.
  generalize dependent gd'.
  generalize dependent d'.
  induction Hf; intros.
  - sauto lq: on.
  - sauto lq: on rew: off.
  - sauto lq: on rew: off.
  - sinvert H. sinvert H2. admit.
Admitted.
  (* generalize dependent n. induction g; cbn in *; intros;
  sinvert Hf'; sinvert Hf; [apply IH; assumption | | | |]; sinvert He; constructor; try assumption;
  try (eapply IHg; [| eassumption | eassumption | |]; assumption);
  destruct H6; [left; assumption | right | left | right; assumption]. Abort. *)
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
(* NOTE: had to strengthen this to, carry along the agreement. *)
Theorem sub_preserves_env : forall n G D,
  EnvTyped n G ->
  Subtype G D ->
  EnvTyped n D /\ Agree Inert n n (fv G) (fv D).
Proof.
  intros n G D He Hs. generalize dependent n. induction Hs; cbn in *; intros.
  - shelve. (* eapply fill_preserves_env; [apply H | | | |]; eassumption. *)
  - admit.
  - admit.
  - admit. 
  (* removed cases
  - sinvert He. assumption.
  - sinvert He. assumption. *)
  - admit.
  - admit.
  Unshelve. Abort.
(*
Qed.
Hint Resolve sub_preserves_env : core.
*)
