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
  Sets
  Terms
  Types
  Typing.

Theorem maximal_push : forall e e' eta p,
  Step eta e e' p ->
  MaximalOn (fv e) eta ->
  MaximalPrefix p.
Proof.
  cbn. intros e e' eta p Hs Hm. generalize dependent Hm. induction Hs; cbn in *; intros.
  - constructor.
  - constructor.
  - destruct (Hm _ eq_refl) as [p' [Hn Hp]]. rewrite H in Hn. sinvert Hn. assumption.
  - constructor; [apply IHHs1 | apply IHHs2]; intros; apply Hm; [left | right]; assumption.
  - apply H in IHHs as []. intros. apply Hm. left. assumption.
  - constructor. { assumption. } apply IHHs2. intros. apply Hm. right. assumption.
  - apply IHHs; clear IHHs. intros. destruct (eqb_spec y x0).
    + subst. exists p2. split. { reflexivity. } Abort.

Theorem soundout : forall G e e' s eta p,
    Typed G e s ->
    (* WFTerm (fv G) e -> *)
    WFContext G ->
    EnvTyped eta G ->
    Step eta e e' p ->
    PfxTyped p s
.
Proof.
    intros G e e' s eta p Ht Hwf He Hs.
    generalize dependent e'.
    generalize dependent eta.
    generalize dependent p.
    generalize dependent Hwf.
    induction Ht; cbn in *; intros.
    - sinvert Hs. constructor; [eapply IHHt1 | eapply IHHt2]; eassumption.
    - sinvert Hs. eapply IHHt; clear IHHt; [| | eassumption].
      + eapply hmm'; [left; reflexivity | | | |]; eassumption.
      + assert (A := maps_to_has_type _ _ _ _ He). destruct A as [p' [Hp1 Hp2]]. sinvert Hp2.
        rewrite Hp1 in H9. sinvert H9. eapply catlenvtyped; eassumption.
    - sinvert Hwf. sinvert He. sinvert Hs; constructor; [eapply IHHt1 | eapply IHHt1 | | eapply IHHt2]; eassumption.
    - sinvert Hs; eapply IHHt; [| | eassumption | | | eassumption].
      + eapply hmm'; [right; reflexivity | | | |]; eassumption.
      + eapply catrenvtyped1; try eassumption. apply maps_to_has_type in He as [p' [Hp1 Hp2]].
        rewrite Hp1 in H10. sinvert H10. sinvert Hp2. assumption.
      + eapply hmm'; [right; reflexivity | | | |]; eassumption.
      + assert (A := maps_to_has_type _ _ _ _ He). destruct A as [p' [Hp1 Hp2]].
        rewrite Hp1 in H10. sinvert H10. sinvert Hp2. eapply catrenvtyped2; eassumption.
    - sinvert Hs. constructor.
    - sinvert Hs. constructor.
    - sinvert Hs. assert (A := maps_to_has_type _ _ _ _ He). destruct A as [p' [Hp1 Hp2]].
      rewrite H1 in Hp1. sinvert Hp1. assumption.
    - sinvert H.
    - sinvert Hs. apply wf_fill in Hwf as [Hwfh [Hwfc Hd]]. eapply IHHt2; [| | eassumption].
      + apply wf_fill. repeat split; [assumption | constructor | |]; scongruence.
      + eapply letenvtyped; [| eassumption]. eapply IHHt1; [| eapply maps_to_hole |]; eassumption.
    - sinvert Hs. apply wf_fill in Hwf as [Hwfh [Hwfc Hd]]. eapply IHHt; [| | eassumption].
      + apply wf_fill. repeat split; [assumption | constructor | |]; scongruence.
      + eapply dropenvtyped. eassumption.
Qed.

(*
(x : s, y : s) |- fix(x:s,y:s). rec(x+1,x) : s
|->
cut x = x+1 in y = x in rec(x+1,x)
WRONG!!

We need a real multicut for unfolding recursive calls.
*)
