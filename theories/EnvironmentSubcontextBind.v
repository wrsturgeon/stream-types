(* This file covers Theorems B.11 and 12. *)

From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Derivative
  Environment
  FV
  Hole
  Prefix
  Sets
  Types.

(* A version of B.11 more specific than agreement: the exact same term *)
Theorem env_subctx_bind_equal : forall hole plug n n',
  NoConflict n n' ->
  EnvTyped n (fill hole plug) ->
  EnvTyped n' plug ->
  EnvTyped (env_union n n') (fill hole plug).
Proof.
  intros hole plug n n' Hc Hn Hn'.
  remember (fill hole plug) as ctx eqn:Ef. assert (Hf := Ef). apply reflect_fill in Hf.
  generalize dependent n. generalize dependent n'. generalize dependent Ef.
  induction Hf; sfirstorder.
Qed.
Hint Resolve env_subctx_bind_equal : core.

Lemma or_hyp : forall P Q R,
  ((P \/ Q) -> R) ->
  ((P -> R) /\ (Q -> R)).
Proof. sfirstorder. Qed.
Hint Resolve or_hyp : core.

Lemma agree_union : forall P n n' D D' lhs lhs' lhs'',
  NoConflict n n' ->
  (PropOn P D n <-> PropOn P D' n') ->
  FillWith D  lhs lhs'  ->
  FillWith D' lhs lhs'' ->
  PropOn P lhs' n ->
  PropOn P lhs'' (env_union n n').
Proof.
  intros P n n' D D' lhs lhs' lhs'' Hn Hp Hf Hf' H. generalize dependent P. generalize dependent n.
  generalize dependent n'. generalize dependent D'. generalize dependent lhs''.
  induction Hf; intros; sinvert Hf'; [hauto l: on | | | |];
  intros x [Hfv | Hfv]; try (eapply IHHf; clear IHHf; [| assumption | eassumption | | eassumption];
    [assumption |]; intros x' H'; apply H; try (left; assumption); right; assumption); clear IHHf;
  try assert (A := H _ (or_intror Hfv)); try assert (A := H _ (or_introl Hfv)); destruct A as [p [Hnx HP]];
  exists p; cbn; (destruct (n' x) eqn:E; split; [f_equal; symmetry; eapply Hn | | |]); eassumption.
Qed.
Hint Resolve agree_union : core.

(* Theorem B.11 *)
(* The only reason this is difficult is the extra disjunction in the environment-typing rule for semicolon contexts,
 * and that's why we need the `agree_union` lemma. *)
Theorem env_subctx_bind : forall hole plug plug' n n',
  NoConflict n n' ->
  EnvTyped n (fill hole plug) ->
  EnvTyped n' plug' ->
  Agree n n' plug plug' ->
  EnvTyped (env_union n n') (fill hole plug').
Proof.
  intros hole plug plug' n n' Hc Hn Hn' [Ham Hae].
  remember (fill hole plug) as ctx eqn:Hf. apply reflect_fill in Hf.
  remember (fill hole plug') as ctx' eqn:Hf'. apply reflect_fill in Hf'.
  generalize dependent plug'. generalize dependent n. generalize dependent n'. generalize dependent ctx'.
  induction Hf; cbn in *; intros; [sinvert Hf'; apply env_typed_weakening; assumption | | | |];
  sinvert Hf'; sinvert Hn; constructor; try (eapply IHHf; eassumption); clear IHHf;
  try (apply env_typed_weakening_alt; assumption); (* everything from here on is just the extra disjunction *)
  (destruct H5; [left | right]); try (apply prop_on_weakening_alt; assumption); eapply agree_union; eassumption.
Qed.
Hint Resolve env_subctx_bind : core.

(* TODO: what's the notation in Theorem B.12? *)
