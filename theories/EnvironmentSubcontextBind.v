(* This file covers Theorems B.11 and 12. *)

From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  Hole
  Prefix.

(* A version of B.11 more specific than agreement: the exact same term *)
Theorem environment_subcontext_bind_straightforward : forall hole plug n n',
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

(* Theorem B.11 *)
Theorem environment_subcontext_bind : forall hole plug plug' n n',
  NoConflict n n' ->
  EnvTyped n (fill hole plug) ->
  EnvTyped n' plug' ->
  Agree n n' plug plug' ->
  EnvTyped (env_union n n') (fill hole plug').
Proof.
  intros hole plug plug' n n' Hc Hn Hn' [Ham Hae].
  remember (fill hole plug) as ctx eqn:Ef. assert (Hf := Ef). apply reflect_fill in Hf.
  remember (fill hole plug') as ctx' eqn:Ef'. assert (Hf' := Ef'). apply reflect_fill in Hf'.
  generalize dependent plug'. generalize dependent n. generalize dependent n'. generalize dependent Ef.
  generalize dependent ctx'. induction Hf; cbn in *; intros; subst. { hauto l: on. }
  - sinvert Ef. sinvert Hn. sinvert Hf'. constructor; [| hauto l: on]. eapply IHHf; sfirstorder.
  - simple_inverting. constructor; [hauto l: on |]. eapply IHHf; sfirstorder.
  - simple_inverting. constructor; [qauto l: on | hauto l: on |]. destruct H9. { left. hauto l: on. }
    right. cbn in *. intros. eexists. Abort.
