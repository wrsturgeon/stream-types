From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Prefix
  Semantics
  SinkTerm
  Sets
  Terms
  Types
  Typing
  Nullable
  Inertness
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


Theorem soundout : forall G e e' s eta p,
    Typed G e s ->
    WFContext G ->
    EnvTyped eta G ->
    Step eta e e' p ->
    PrefixTyped p s.
Proof.
    intros G e e' s eta p Ht Hwf Heta Hstep.
    generalize dependent G.
    generalize dependent s.
    (* induction Hstep; intros.
    - admit.
    - admit.
    - admit.
    - sinvert Ht; admit.
    - sinvert Hstep.
      assert (~fv G z) by hauto q: on use:wf_fill_reflect.
      eapply IHHt; [| | eauto].
      + admit.
      + admit. (*eapply catlenvtyped; eauto; sauto l: on use: maps_to_has_type.*)
    - sinvert Hwf. sinvert Heta. sinvert Hstep.
      + constructor. eapply IHHt1; sauto lq: on rew: off.
      + constructor. eapply IHHt1; sauto lq: on rew: off. eauto. sauto lq: on rew: off.
    - sinvert Hstep; eapply IHHt; [| | eauto | | | eauto].
      + eapply hmm'_reflect; eauto.
      + eapply catrenvtyped1; admit.
      + eapply hmm'_reflect; eauto.
      + assert (PrefixTyped (PfxCatBoth p1 p2) (Types.TyDot s t)) by hauto l: on use:maps_to_has_type_reflect.
        sinvert H4.
        eapply catrenvtyped2; eauto. 
    - sauto lq: on.
    - sauto lq: on.
    - sinvert Hstep. 
      sauto use: maps_to_has_type_reflect.
    - sfirstorder.
    - sinvert Hstep. 
      assert (PrefixTyped p0 s). eapply IHHt1; eauto. sfirstorder use:maps_to_hole_reflect.
      eapply IHHt2; [ | | eauto].
      + eapply wf_fill_reflect. eauto. sfirstorder use:wf_fill_reflect.
      + eapply letenvtyped; eauto.
      admit.
        (* eapply agree_step_inert; eauto. *)
    - sinvert Hstep. eapply IHHt; [ | | eauto]. eapply wf_fill_reflect. eauto. sfirstorder use:wf_fill_reflect. admit. *)
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
