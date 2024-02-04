From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Derivative
  Ind
  Inert
  Nullable
  Prefix
  Semantics
  SinkTerm
  Sets
  Terms
  Types
  Typing.

(* Theorem agree_step_inert : forall e e' eta p S x s,
  Inert e ->
  Subset (fv e) S -> (*automatic from typing derivatino*)
  Step eta e e' p ->
  PrefixTyped p s ->
  Agree Inert eta (singleton_env x p) S (singleton_set x)
.
Proof.
  intros.
  unfold Agree. split; intros.
  - assert (MaximalOn (fv e) eta); [eapply prop_on_contains; eauto |].
    assert (MaximalPrefix p) by sfirstorder use:maximal_push.
    exists p. sinvert H6. unfold singleton_env. hauto lq: on use:eqb_refl. 
  - assert (EmptyOn (fv e) eta); [eapply prop_on_contains; eauto |].
    assert (EmptyPrefix p) by hauto lb: on drew: off use:empty_push_inert.
    exists p. sinvert H6. unfold singleton_env. hauto lq: on use:eqb_refl.
Qed. *)

Definition Preserves i eta p s :=
    (MaximalOn s eta -> MaximalPrefix p)
    /\
    (i = Inert -> EmptyOn s eta -> EmptyPrefix p)
.

Theorem preserves_to_agree : forall i eta p s S' S x,
Subset S' S ->
Preserves i eta p S' ->
Agree i eta (singleton_env x p)
  S (fv (CtxHasTy x s))
.
Proof.
intros.
unfold Preserves in *.
unfold Agree in *.
destruct H0 as [A B].
split; intros.
+ assert (MaximalOn S' eta) by best use:prop_on_contains.
  cbn. intros. exists p. destruct H2. hauto lq: on use:eqb_refl.
+ assert (EmptyOn S' eta) by best use:prop_on_contains.
  cbn. intros. exists p. destruct H3. hauto lq: on use:eqb_refl.
Qed.


Definition P_sound g (e : term) s eta (e' : term) p :=
  WFContext g ->
  EnvTyped eta g ->
    PrefixTyped p s /\
    (forall g' s', Derivative p s s' -> ContextDerivative eta g g' -> Typed g' e' s') /\
    Preserves Jumpy eta p (fv e)
.

Theorem sound : forall G e s eta e' p,
    Typed G e s ->
    Step eta e e' p ->
    P_sound G e s eta e' p.
Proof.
    apply (lex_ind P_sound); unfold P_sound in *; intros; admit.
Admitted.

Definition P_sound_args g_in (e : argsterm) g_out eta_in (e' : argsterm) g_out' eta_out :=
  WFContext g_out ->
  WFContext g_in ->
  EnvTyped eta_in g_in ->
    EnvTyped eta_out g_out /\
    SetEq (dom eta_out) (fv g_out) /\
    (Agree Jumpy eta_in eta_out (fv g_in) (fv g_out)) /\
    (forall g_in', ContextDerivative eta_in g_in g_in' -> ArgsTyped g_in' e' g_out')
.

(* this is basically how this theorem needs to go, but we have to figure out how to tie the knot with the regular soundness theorem. *)
Theorem soundargs : forall g_in e g_out g_out' eta_in e' eta_out,
    ArgsTyped g_in e g_out ->
    ArgsStep eta_in g_out e e' g_out' eta_out ->
    P_sound_args g_in e g_out eta_in e' g_out' eta_out.
Proof.
  intros.
  generalize dependent g_in.
  induction H0; unfold P_sound_args in *; intros.
  - best.
  - sinvert H1. 
    edestruct sound as [A [B C]]; eauto.
  split; try split; try split.
    + eapply env_typed_singleton; eauto.
    + sfirstorder use:dom_singleton.
    + sfirstorder use:dom_singleton.
    + eapply preserves_to_agree; [|eauto]. sfirstorder use:typing_fv.
    + sauto lq: on.
  - sinvert H. sinvert H0.
    edestruct IHArgsStep1 as [A [B [C D]]]; eauto.
    edestruct IHArgsStep2 as [E [F [G H]]]; eauto.
    split; try split; try split.
    + eapply env_typed_comma; [| eauto | eauto]. hauto q: on.
    + hauto q: on.
    + hauto drew: off.
    + admit.
    + sauto lq: on rew: off.
  - sinvert H1; sinvert H2; sinvert H4; sinvert H3.
    edestruct IHArgsStep as [A [B [C D]]]; eauto.
    split; try split; try split.
    + eapply env_typed_semic; [| eauto| sfirstorder use:empty_env_for_typed | hauto lq: on use:empty_env_for_empty] . 
      clear D; clear C; clear H13; clear H9; clear H11; clear H; clear H0; clear IHArgsStep.
      assert (Subset (fv g3) (dom eta)) by best use:envtyped_dom.
      assert (Subset (fv g0) (dom eta)) by best use:envtyped_dom.
      hauto lq:on rew: off use:empty_env_for_dom.
    + cbn. hauto q: on use:empty_env_for_dom.
    + cbn. hauto q: on use:empty_env_for_dom.
    + admit.
    + intros. sinvert H1. econstructor. eauto.
      destruct H13.
      * assert (H00 : D' = g3) by best use:context_derivative_emp'.
        destruct H00.
        eauto.
      (* contradictory. *)
      * sfirstorder.
  - sinvert H0. sinvert H1. sinvert H3. sinvert H2.
    edestruct IHArgsStep1 as [A [B [C D]]]; eauto.
    edestruct IHArgsStep2 as [E [F [G H']]]; eauto.
    split; try split; try split.
    + eapply env_typed_semic; [| eauto | eauto | eauto]. hauto q: on.
    + hauto q: on.
    + hauto drew: off.
    + admit.
    + sauto q: on.
Admitted.

(* let x = e in e' | *)

(*
(x : s, y : s) |- fix(x:s,y:s). rec(x+1,x) : s
|->
cut x = x+1 in y = x in rec(x+1,x)
WRONG!!

We need a real multicut for unfolding recursive calls.


y : bool |- 3 : int             x : int ; u : int |= (x;u)
----------------------------------------------------
x : int ; y : bool |- let u = 3 in (x;u) : int . int

*)