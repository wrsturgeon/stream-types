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
  Typing.

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
  - intros. eapply IHStep.
    simpl in H1.
    edestruct (H1 z) as [p [A B]]; [sfirstorder|].
    assert (p = PfxParPair p1 p2) by scongruence.
    subst.
    sinvert B.
    unfold MaximalOn. unfold PropOn. intros.
    unfold PropOnItem.
    admit.
Admitted.

(* NOT CLEAR ABOUT RECURSION. when you unfold a fixpoint, you might get a thing that's not reactive at toplevel.
1, ::, (;) are not reactive.
*)

(* terms need to be primed. The output of EVERY STEP is inert. it won't produce
anything with the empty prefix, because otherwise it would have earlier. This problem *can only happen* when you're kicking off a function (and on recursive calls).*)

Theorem empty_push_reactive : forall e e' eta p,
  reactive e ->
  Step eta e e' p ->
  EmptyOn (fv e) eta ->
  EmptyPrefix p.
Proof.
  intros.
  induction H0; sinvert H.
  - sauto lq: on.
  - qauto l: on.
  - sauto lq: on rew: off.
  - eapply IHStep. eauto. admit. (* correct. *)
  - eapply IHStep. eauto. admit. (* corrrect *) 
  - admit.
  - hauto drew: off.
  - admit.
Admitted.


Theorem agree_step : forall e e' eta p G x s,
  (forall x0, fv e x0 -> fv G x0) ->
  Step eta e e' p ->
  PfxTyped p s ->
  Agree eta (singleton_env x p) G (CtxHasTy x s)
.
Proof.
  intros.
  unfold Agree. split; split; intros; unfold MaximalOn in *; unfold EmptyOn in *; unfold PropOn in *; unfold PropOnItem in *; intros.
  - assert (MaximalPrefix p) by sfirstorder use:maximal_push.
    exists p. sinvert H3. unfold singleton_env. sauto lq: on use:eq_id_refl.
  -


Theorem step_reactive : forall e e' eta p,
  reactive e ->
  Step eta e e' p ->
  reactive e'.
Proof.
  intros.
  induction H0; sinvert H.
  - sfirstorder.
  - sfirstorder.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on rew: off use:sink_reactive.
  - sauto lq: on.
  - sauto lq: on.
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
    induction Hty; intros p eta e0' Heta Hstep.
    - cbn in *. sauto q: on.
    - sinvert Hstep.
      assert (~fv G z) by hauto q: on use:wf_fill.
      eapply IHHty; [| | eauto].
      + qauto l: on use: hmm'.
      + eapply catlenvtyped; eauto; sauto l: on use: maps_to_has_type.
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
