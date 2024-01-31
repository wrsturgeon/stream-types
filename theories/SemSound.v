From Coq Require Import
    Program.Equality
    String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Prefix
  Semantics
  SinkTm
  Sets
  Terms
  Types
  Typing
  Nullable
  .

Theorem maximal_push : forall e e' eta p,
  Step eta e e' p ->
  MaximalOn (fv e) eta ->
  MaximalPrefix p.
Proof.
  intros.
  generalize dependent H0.
  induction H.
  - hauto l: on.
  - hauto l: on.
  - qauto l: on.
  - sauto l: on.
  - sauto l: on.
  - sauto l: on.
  - admit.
Admitted.

Theorem empty_push_inert : forall e e' eta p ,
  Inert e ->
  Step eta e e' p ->
  EmptyOn (fv e) eta ->
  EmptyPrefix p /\ Inert e'.
Proof.
  intros.
  induction H0; intros.
  - sauto lq: on.
  - sauto lq: on.
  - qauto l: on.
  - sauto.
  - sinvert H.
  - sauto lq: on.
  - sinvert H. 
    edestruct IHStep as [A B]; [eauto | admit |]. (* obvious, gotta compute envs. *)
    split; sauto lq: on rew: off.
  - sinvert H. 
    edestruct IHStep as [A B]; [eauto | admit |]. (* obvious, gotta compute envs. *)
    split; sauto lq: on rew: off.
  - assert (exists p, n z = Some p /\ EmptyPrefix p) by sfirstorder.
    destruct H3 as [p'' [A B]].
    destruct (ltac:(sfirstorder) : PfxCatBoth p1 p2 = p'').
    sinvert B.
  - sinvert H. edestruct IHStep1; [eauto | hauto q: on use:prop_on_contains|].
    assert (EmptyOn (set_minus (fv e2) (singleton_set x)) eta) by hauto q: on use:prop_on_contains.
    edestruct IHStep2; [eauto | admit |].
    sauto lq: on.
  - sinvert H. edestruct IHStep; [eauto | admit |]. sauto lq: on.
Admitted.

Theorem agree_step_inert : forall e e' eta p G x s,
  Inert e ->
  SubsetOf (fv e) (fv G) -> (*automatic from typing derivatino*)
  Step eta e e' p ->
  PrefixTyped p s ->
  Agree eta (singleton_env x p) G (CtxHasTy x s)
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
Qed.


Theorem soundout : forall G e e' s eta p,
    Typed G e s ->
    (* WFTerm (fv G) e -> *)
    WFContext G ->
    EnvTyped eta G ->
    Step eta e e' p ->
    PrefixTyped p s.
Proof.
    intros G e e' s eta p Ht Hwf He Hs.
    generalize dependent e'.
    generalize dependent eta.
    generalize dependent p.
    induction Ht; intros p eta e0' Heta Hstep.
    - cbn in *. sauto q: on.
    - sinvert Hstep.
      assert (~fv G z) by hauto q: on use:wf_fill_reflect.
      eapply IHHt; [| | eauto].
      + admit.
      + admit. (*eapply catlenvtyped; eauto; sauto l: on use: maps_to_has_type.*)
    - sinvert HwfG; sinvert Heta. sinvert Hstep.
      + constructor. eapply IHHty1; eauto.
      + constructor. eapply IHHty1; eauto. eauto. eauto.
    - sinvert Hstep; eapply IHHty; [| | eauto | | | eauto].
      + eapply hmm'; eauto.
      + eapply catrenvtyped1; eauto. sauto l: on use: maps_to_has_type.
      + eapply hmm'; eauto.
      + assert (PfxTyped (PfxCatBoth p1 p2) (Types.TyDot s t)) by sauto l: on use: maps_to_has_type.
        sinvert H2.
        eapply catrenvtyped2; eauto. 
    - sauto lq: on.
    - sauto lq: on.
    - sinvert Hstep. 
      sauto use: maps_to_has_type.
    - sfirstorder.
    - sinvert Hstep. eapply IHHty2; [ | | eauto].
      + sauto l: on use:wf_fill.
      + eapply letenvtyped; [ | | eauto].
        eapply IHHty1; [| | eauto]. sfirstorder use:wf_fill. sfirstorder use:maps_to_hole.
    - sinvert Hstep. eapply IHHty; [ | | eauto]. hauto lq: on rew: off use: wf_fill.
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
