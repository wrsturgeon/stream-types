From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  EnvConcat
  Environment
  FV
  Prefix
  PrefixConcat
  Semantics
  Sets
  Terms
  Types
  Typing.

(* Theorem B.45 *)
Theorem maximal_semantics_aux : forall n e e' p',
  Step n e e' p' ->
  MaximalOn (fv e) n ->
  MaximalPrefix p'.
Proof.
  intros n e e' p' Hs Hm. generalize dependent Hm. induction Hs; intros.
  - (* S-Var (case 1) *)
    specialize (Hm _ eq_refl) as [p' [Hp'1 Hp'2]]. scongruence.
  - (* S-Par-R (case 4) *)
    (* If we were follwing the written proof, this works:
    assert (A1 : forall x, fv e1 x -> exists p, n x = Some p) by sfirstorder.
    assert (A2 : forall x, fv e2 x -> exists p, n x = Some p) by sfirstorder. *)
    constructor; [apply IHHs1 | apply IHHs2]; intros x H; apply Hm; [left | right]; assumption.
  - (* S-Par-L (case 7) *)
    simpl fv in Hm. (* fv(<let (x, y) = z in e>) = {z} union fv(e) \ {x, y} *)
    assert (A : MaximalPrefix (PfxParPair p1 p2)). { (* parPair(p1, p2) maximal *)
      destruct (Hm z) as [p [Hp1 Hp2]]. { left. reflexivity. } congruence. } (* proving the above *)
    sinvert A. (* inversion on (4), defined above *)
    assert (A : forall u, fv e u -> exists p',
      MaximalPrefix p' /\
      env_union n (env_union (singleton_env x p1) (singleton_env y p2)) u = Some p'). {
        intros s Hfv. cbn in *. (* proving the above... *)
        destruct (eqb_spec y s). { subst. eexists. split; [| reflexivity]; assumption. }
        destruct (eqb_spec x s). { subst. eexists. split; [| reflexivity]. assumption. }
        edestruct Hm as [p [Hp1 Hp2]]. { right. repeat split; eassumption. } exists p. split; assumption. }
    apply IHHs. (* proof proceeds by IH *)
    cbn. intros s Hfv. specialize (A _ Hfv) as [p [Hp1 Hp2]]. exists p. split; assumption.
  - (* S-Cat-R-1 (case 5) *)
    contradiction H. apply IHHs. eapply prop_on_subset; [| eassumption]. left. assumption.
  - (* S-Cat-R-2 (case 6) *)
    constructor; [eapply IHHs1 | eapply IHHs2];
    (eapply prop_on_subset; [| eassumption]); [left | right]; assumption.
  - (* S-Cat-L-1 (case 8) *)
    specialize (Hm _ (or_introl eq_refl)) as [c [E C]]. rewrite H in E. sinvert E. sinvert C. (* contradiction *)
  - (* S-Cat-L-2 (case 9) *)
    assert (A : MaximalPrefix (PfxCatBoth p1 p2)). { (* parPair(p1, p2) maximal *)
      destruct (Hm z) as [p [Hp1 Hp2]]. { left. reflexivity. } congruence. } (* proving the above *)
    sinvert A. (* inversion on (4), defined above *)
    assert (A : forall u, fv e u -> exists p',
      MaximalPrefix p' /\
      env_union n (env_union (singleton_env x p1) (singleton_env y p2)) u = Some p'). {
        intros s Hfv. cbn in *. (* proving the above... *)
        destruct (eqb_spec y s). { subst. eexists. split; [| reflexivity]; assumption. }
        destruct (eqb_spec x s). { subst. eexists. split; [| reflexivity]. assumption. }
        edestruct Hm as [p [Hp1 Hp2]]. { right. repeat split; eassumption. } exists p. split; assumption. }
    apply IHHs. (* proof proceeds by IH *)
    cbn. intros s Hfv. specialize (A _ Hfv) as [p [Hp1 Hp2]]. exists p. split; assumption.
  - (* S-Eps-R (case 2) *)
    constructor.
  - (* S-One-R (case 3) *)
    constructor.
  - (* S-Cut (case 22) *)
    assert (Hp : MaximalPrefix p). {
      clear Hs1 Hs2 IHHs2. cbn in *. apply IHHs1. clear IHHs1. intros x' H'. apply Hm. left. assumption. }
    assert (A : forall y, fv e2 y -> exists p',
      MaximalPrefix p' /\
      env_union n (singleton_env x p) y = Some p'). {
        intros y Hy. cbn in *. destruct (eqb_spec x y). { subst. eexists. split; [| reflexivity]. assumption. }
        specialize (Hm y). destruct Hm as [pr [H1' H2']]; [right | eexists]; split; eassumption. }
    apply IHHs2. intros y Hy. specialize (A _ Hy) as [e [He1 He2]]. eexists. split; eassumption.
Qed.
Hint Resolve maximal_semantics_aux : core.

(* Theorem B.46 *)
Theorem maximal_semantics : forall n e e' p G s,
  Step n e e' p ->
  Typed G e s ->
  MaximalOn (fv G) n ->
  MaximalPrefix p.
Proof.
  intros n e e' p G s Hs Ht Hm. assert (Hf := typing_fv _ _ _ Ht).
  eapply maximal_semantics_aux. { eassumption. } eapply prop_on_subset; eassumption.
Qed.
Hint Resolve maximal_semantics : core.

(* Theorem B.47 *)
Theorem maximal_semantics_extn : forall n e e' p n' n'' e'' p',
  Step n e e' p ->
  MaximalPrefix p ->
  EnvConcat n n' n'' ->
  Step n'' e e'' p' ->
  p = p'.
Proof.
  intros n e e' p n' n'' e'' p' Hs Hm He Hs'. generalize dependent n'. generalize dependent n''.
  generalize dependent e''. generalize dependent p'. generalize dependent Hm.
  induction Hs; cbn in *; intros.
  - sinvert Hs'. Abort.
