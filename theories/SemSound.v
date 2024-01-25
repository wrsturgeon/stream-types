From LambdaST Require Import
    Terms
    Semantics
    Typing
    Prefix
    Environment
    Hole
    Context.
Require Import Coq.Program.Equality.

From Hammer Require Import Tactics.


Theorem soundout : forall G e e' s eta p,
    Typed G e s ->
    Step eta e e' p ->
    wf e ->
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
    - sauto lq: on rew: off.
    - sinvert Hwfe; sinvert Hstep; eapply IHHty.
      + eauto.
      + eauto.
      + admit.
      + admit.
    - sinvert Hwfe. admit.
    - sinvert Hwfe. admit.
    - sinvert Hwfe. admit.
    - sinvert Hwfe. admit.
    - sinvert Hwfe. admit.
    - admit.
    - admit.
Admitted.