From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Ident
  Prefix
  Semantics
  Terms
  Typing.
From Coq Require Import
    Program.Equality.
From Hammer Require Import
  Tactics.

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
Admitted.


Theorem soundout : forall G e e' s eta p,
    Typed G e s ->
    (* WFTerm (fv G) e -> *)
    WFContext G ->
    EnvTyped eta G ->
    Step eta e e' p ->
    PfxTyped p s
.
Proof.
    intros G e e' s eta p Hty HwfG.
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
      + eapply letenvtyped; [| eauto].
        eapply IHHty1; [| | eauto]. sfirstorder use:wf_fill. sfirstorder use:maps_to_hole.
    - sinvert Hstep. eapply IHHty; [ | | eauto]. hauto lq: on rew: off use: wf_fill.
Admitted.

(*

(x : s, y : s) |- fix(x:s,y:s). rec(x+1,x) : s
|->
cut x = x+1 in y = x in rec(x+1,x)
WRONG!!

We need a real multicut for unfolding recursive calls.
*)
