From LambdaST Require Import
    Terms
    Semantics
    Typing
    Prefix
    Environment
    Hole
    FV
    Context.
Require Import Coq.Program.Equality.

From Hammer Require Import Tactics.

Theorem maximalpush : forall e e' eta p,
  Step eta e e' p ->
  MaximalOn (fv e) eta ->
  Maximal p.
Proof.
  intros.
  generalize dependent H0.
  induction H; intros.
  - sauto lq: on.
  - sauto lq: on.
  - qauto l: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - admit.
  - admit.
Admitted.



Theorem soundout : forall G e e' s eta p,
    Typed G e s ->
    Step eta e e' p ->
    wf (fv G) e ->
    wf_ctx G ->
    EnvTyped eta G ->
    PfxTyped p s
.
Proof.
    intros G e e' s eta p Hty.
    generalize dependent e'.
    generalize dependent eta.
    generalize dependent p.
    induction Hty; intros p eta e0' Hstep Hwfe HwfG Heta.
    - sinvert Hwfe. cbn in *. sauto q: on.
    - sinvert Hwfe; sinvert Hstep.
      assert (~fv G x) by sfirstorder use:fv_fill.
      assert (~fv G y) by sfirstorder use:fv_fill.
      assert (PfxTyped (PfxParPair p1 p2) (Types.TyPar s t)) by qauto l:on use: maps_to_has_type.
      sinvert H1.
      eapply IHHty.
      + eauto.
      + eapply wf_iff; [| eauto]. intro. admit. (* i think we can do this. *)
      + apply wf_fill in HwfG. destruct HwfG as [A [B C]].
        apply wf_fill.
        (* here, we need to know that x and y are not free in G.*)
        split; try split. sfirstorder. sauto l: on. cbn in *. sfirstorder use:fv_fill.
      + eapply fill_replace; [|eauto| |]. admit.
        * eapply envtyped_comma; [| eapply envtyped_singleton; eauto | eapply envtyped_singleton; eauto]. admit.
        * admit. 
    - sinvert Hwfe; sinvert HwfG; sinvert Heta. sinvert Hstep; admit.
    - sinvert Hwfe. admit.
    - sinvert Hwfe. admit.
    - sinvert Hwfe. admit.
    - sinvert Hwfe. apply wf_fill in HwfG. 
      destruct HwfG as [U []]. sinvert H. apply fv_fill in H1.
      sauto use: maps_to_has_type.
    - sfirstorder.
    - sinvert Hstep.
Admitted.

(*

(x : s, y : s) |- fix(x:s,y:s). rec(x+1,x) : s
|->
cut x = x+1 in y = x in rec(x+1,x)
WRONG!!

We need a real multicut for unfolding recursive calls.
*)