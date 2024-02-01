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
  | SubCommaWkn : forall g d,
      Subtype (CtxComma g d) g
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

Theorem subtype_fv_subset : forall g g',
  Subtype g g' ->
  Subset (fv g') (fv g).
Proof.
  intros.
  induction H; unfold Subset in *; cbn; try sfirstorder.
  intros.
  hauto q: on use:fv_fill.
Qed.


Lemma fill_preserves_env : forall (d d' : context) (g : hole) (gd gd' : context),
  Fill g d gd ->
  Fill g d' gd' ->
  (forall n : env, EnvTyped n d -> EnvTyped n d') ->
  forall n : env,
  Agree Inert n n (fv d) (fv d') ->
  EnvTyped n gd ->
  EnvTyped n gd'.
Proof.
  intros d d' g gd gd' Hf.
  generalize dependent gd'.
  generalize dependent d'.
  induction Hf; intros; [sauto lq: on | sauto lq: on | sauto lq: on | | ];
  sinvert H; sinvert H2; sinvert H8; constructor; eauto; [right | left];
  eapply prop_on_fill in H; eauto;
  qauto l: on use:prop_on_fill.
Qed.

(* Theorem B.35 *)
(* NOTE: had to strengthen this to, carry along the agreement. *)
Theorem sub_preserves_env : forall n G D,
  EnvTyped n G ->
  Subtype G D ->
  EnvTyped n D /\ Agree Inert n n (fv G) (fv D).
Proof.
  intros n G D He Hs. generalize dependent n. induction Hs; intros.
  - assert (EnvTyped n d) by sfirstorder use:maps_to_hole_reflect.
   edestruct IHHs; eauto.
   split.
    + eapply fill_preserves_env; [ | | | eauto | ]; eauto. hauto l: on.
    + assert (Subset (fv gd') (fv gd)) by sauto lq: on rew: off use:subtype_fv_subset.
      unfold Subset in *. hauto q: on.
  - split. eauto. sfirstorder.
  - sauto lq: on  rew: off.
  - sauto lq: on rew: off.
  - sauto lq: on rew: off.
  - sauto lq: on rew: off.
  - sauto lq: on rew: off.
  - sauto.
  - sauto.
Qed.
