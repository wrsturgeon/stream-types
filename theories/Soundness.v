From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Environment
  FV
  Prefix
  Semantics
  Sets
  Terms.

(* Theorem 3.1, page 11 *)
Theorem maximal_semantics : forall n e e' p',
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
  - (* S-Eps-R *)
    constructor.
  - (* S-One-R *)
    constructor.
Qed.
