(* This file covers Theorems B.11 and 12. *)

From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Prefix
  Sets.

(* A version of B.11 more specific than agreement: the exact same term *)
Theorem environment_subcontext_bind_equal : forall hole plug n n',
  NoConflict n n' ->
  EnvTyped n (fill hole plug) ->
  EnvTyped n' plug ->
  EnvTyped (env_union n n') (fill hole plug).
Proof.
  intros hole plug n n' Hc Hn Hn'.
  remember (fill hole plug) as ctx eqn:Ef. assert (Hf := Ef). apply reflect_fill in Hf.
  generalize dependent n. generalize dependent n'. generalize dependent Ef.
  induction Hf; sfirstorder.
Qed.
Hint Resolve environment_subcontext_bind_equal : core.

Lemma or_hyp : forall P Q R,
  ((P \/ Q) -> R) ->
  ((P -> R) /\ (Q -> R)).
Proof. sfirstorder. Qed.
Hint Resolve or_hyp : core.

Lemma agree_union : forall P n n' D D' lhs lhs' lhs'',
  NoConflict n n' ->
  (PropOn P D n <-> PropOn P D' n') ->
  FillWith D  lhs lhs'  ->
  FillWith D' lhs lhs'' ->
  PropOn P lhs' n ->
  PropOn P lhs'' (env_union n n').
Proof.
  intros P n n' D D' lhs lhs' lhs'' Hn Hp Hf Hf' H. generalize dependent P. generalize dependent n.
  generalize dependent n'. generalize dependent D'. generalize dependent lhs''.
  induction Hf; intros; sinvert Hf'. (* (sinvert Hf') inverts hole-filling *)
  - apply Hp in H. (* Use agreement to convert (PropOn P D n) to (PropOn P lhs'' n') *)
    cbn in *. (* Convert (PropOn P lhs'' (union n n')) to (Forall (prop_on_item P (union n n')) (fv_ctx lhs'')) *)
    intros. (* Instead of `Forall_impl`, since we're not working with lists, intro the in-this-set hypothesis *)
    apply H in H0 as [p [Hn' HP]]. (* From (fv_ctx lhs'' x), infer (exists p, n' x = Some p /\ P p) *)
    exists p. (* From what we just found: (n' x = Some p) *)
    rewrite Hn'. (* Drop it into the match scrutinee *)
    split. { reflexivity. } assumption. (* easy *)
  - cbn. intros x Hfv. (* Obtain the arbitrary `x` that tests membership and make it specific *)
    destruct Hfv as [Hfv | Hfv]. (* x is in the free variables of *either* lhs'0 *or* rhs *)
    + eapply IHHf; clear IHHf; [| assumption | eassumption | | eassumption]; [assumption |]. (* Order matters! *)
      cbn. cbn in H. intros. apply H. left. assumption. (* Easy to show (PropOn P lhs' n) *)
    + clear IHHf. cbn in *. assert (A := H _ (or_intror Hfv)). destruct A as [p [Hnx HP]]. exists p. (* find (n x) *)
      destruct (n' x) eqn:E; split; [f_equal; symmetry; eapply Hn | | |]; eassumption. (* no conflict *)
  - cbn. intros x Hfv. (* Obtain the arbitrary `x` that tests membership and make it specific *)
    destruct Hfv as [Hfv | Hfv]. (* x is in the free variables of *either* lhs'0 *or* rhs *)
    + clear IHHf. cbn in *. assert (A := H _ (or_introl Hfv)). destruct A as [p [Hnx HP]]. exists p. (* find (n x) *)
      destruct (n' x) eqn:E; split; [f_equal; symmetry; eapply Hn | | |]; eassumption. (* use no-conflict *)
    + eapply IHHf; clear IHHf; [| assumption | eassumption | | eassumption]; [assumption |]. (* Order matters! *)
      cbn. cbn in H. intros. apply H. right. assumption. (* Easy to show (PropOn P rhs' n) *)
  - cbn. intros x Hfv. (* Obtain the arbitrary `x` that tests membership and make it specific *)
    destruct Hfv as [Hfv | Hfv]. (* x is in the free variables of *either* lhs'0 *or* rhs *)
    + eapply IHHf; clear IHHf; [| assumption | eassumption | | eassumption]; [assumption |]. (* Order matters! *)
      cbn. cbn in H. intros. apply H. left. assumption. (* Easy to show (PropOn P lhs' n) *)
    + clear IHHf. cbn in *. assert (A := H _ (or_intror Hfv)). destruct A as [p [Hnx HP]]. exists p. (* find (n x) *)
      destruct (n' x) eqn:E; split; [f_equal; symmetry; eapply Hn | | |]; eassumption. (* no conflict *)
  - cbn. intros x Hfv. (* Obtain the arbitrary `x` that tests membership and make it specific *)
    destruct Hfv as [Hfv | Hfv]. (* x is in the free variables of *either* lhs'0 *or* rhs *)
    + clear IHHf. cbn in *. assert (A := H _ (or_introl Hfv)). destruct A as [p [Hnx HP]]. exists p. (* find (n x) *)
      destruct (n' x) eqn:E; split; [f_equal; symmetry; eapply Hn | | |]; eassumption. (* use no-conflict *)
    + eapply IHHf; clear IHHf; [| assumption | eassumption | | eassumption]; [assumption |]. (* Order matters! *)
      cbn. cbn in H. intros. apply H. right. assumption. (* Easy to show (PropOn P rhs' n) *)
Qed.
Hint Resolve agree_union : core.

(* Theorem B.11 *)
(* The only reason this is difficult is the extra disjunction in the environment-typing rule for semicolon contexts,
 * and that's why we need the `agree_union` lemma. *)
Theorem environment_subcontext_bind : forall hole plug plug' n n',
  NoConflict n n' ->
  EnvTyped n (fill hole plug) ->
  EnvTyped n' plug' ->
  Agree n n' plug plug' ->
  EnvTyped (env_union n n') (fill hole plug').
Proof.
  intros hole plug plug' n n' Hc Hn Hn' [Ham Hae].
  remember (fill hole plug) as ctx eqn:Hf. apply reflect_fill in Hf.
  remember (fill hole plug') as ctx' eqn:Hf'. apply reflect_fill in Hf'.
  generalize dependent plug'. generalize dependent n. generalize dependent n'. generalize dependent ctx'.
  induction Hf; cbn in *; intros.
  - (* HoleHere *)
    sinvert Hf'. (* Invert hole-filling to show that plug' = ctx' *)
    apply env_typed_weakening. (* Lemma that EnvTyped of a union <-> EnvTyped of its right argument *)
    assumption. (* and we already know that *)
  - (* HoleCommaL *)
    sinvert Hf'. (* Invert hole-filling to show that ctx' = CtxComma lhs'0 rhs *)
    sinvert Hn. (* Invert environment of (CtxComma lhs' rhs) to show that lhs' and rhs are typed identically *)
    constructor. (* To prove a comma's environment, prove both sides identically *)
    + eapply IHHf; clear IHHf. (* Induction hypothesis *)
      * assumption. (* Already know that n and n' don't conflict *)
      * assumption. (* that n is an environment typed for lhs' *)
      * eassumption. (* ...that n' is an environment typed for plug' *)
      * assumption. (* ...n/n'/D/D' agree on maximality *)
      * assumption. (* ...n/n'/D/D' agree on emptiness *)
      * assumption. (* ...filling lhs with plug' is lhs'0 *)
    + clear IHHf. (* so we can see a damn thing *)
      apply env_typed_weakening_alt. (* Weakening lemma for the left side (n), provided no conflicts *)
      * assumption. (* We already know that n and n' don't conflict *)
      * assumption. (* ...and that n is an environment typed for rhs *)
  - (* HoleCommaR *)
    sinvert Hf'. (* Invert hole-filling to show that ctx' = CtxComma lhs rhs'0 *)
    sinvert Hn. (* Invert environment of (CtxComma lhs' rhs) to show that lhs' and rhs are typed identically *)
    constructor. (* To prove a comma's environment, prove both sides identically *)
    + clear IHHf. (* so we can see a damn thing *)
      apply env_typed_weakening_alt. (* Weakening lemma for the left side (n), provided no conflicts *)
      * assumption. (* We already know that n and n' don't conflict *)
      * assumption. (* ...and that n is an environment typed for lhs *)
    + eapply IHHf; clear IHHf. (* Induction hypothesis *)
      * assumption. (* Already know that n and n' don't conflict *)
      * assumption. (* that n is an environment typed for rhs' *)
      * eassumption. (* ...that n' is an environment typed for plug' *)
      * assumption. (* ...n/n'/D/D' agree on maximality *)
      * assumption. (* ...n/n'/D/D' agree on emptiness *)
      * assumption. (* ...filling rhs with plug' is rhs'0 *)
  - (* HoleSemicL *)
    sinvert Hf'. (* Invert hole-filling to show that ctx' = CtxSemic lhs'0 rhs *)
    sinvert Hn. (* Invert env(CtxSemic lhs' rhs): lhs' & rhs identically, PLUS EmptyOn rhs n \/ MaximalOn lhs' n *)
    constructor. (* Show a semicolon environment by showing lhs & rhs PLUS the above ^^ *)
    + eapply IHHf; clear IHHf. (* Induction hypothesis where ctx' := lhs'0 *)
      * assumption. (* Already know that n and n' don't conflict *)
      * assumption. (* that n is an environment typed for lhs' *)
      * eassumption. (* ...that n' is an environment typed for plug' *)
      * assumption. (* ...n/n'/D/D' agree on maximality *)
      * assumption. (* ...n/n'/D/D' agree on emptiness *)
      * assumption. (* ...filling lhs with plug' is lhs'0 *)
    + clear IHHf. (* so we can see a damn thing *)
      apply env_typed_weakening_alt. (* Show (EnvTyped (env_union n n') rhs) by (EnvTyped n rhs) *)
      * assumption. (* no conflict *)
      * assumption. (* Already know that n is an environment typed for rhs *)
    + clear IHHf. (* so we can see a damn thing *)
      destruct H5. (* We know that either rhs is empty on n or lhs'0 is maximal on it: case analysis *)
      * left. (* Empty case in H5 proves the empty case of the goal *)
        apply empty_on_weakening_alt. (* We already know the left hand of union holds, so weaken away the right *)
        -- assumption. (* no conflict *)
        -- assumption. (* Already know that EmptyOn rhs n *)
      * right. (* Maximal case in H5 proves the maximal case of the goal *)
        eapply agree_union. (* Prove (MaximalOn lhs'0 (env_union n n')) via assumptions & (MaximalOn lhs' n) *)
        -- eassumption. (* Already know that n and n' don't conflict *)
        -- eassumption. (* ...that n/n'/D/D' agree on maximality *)
        -- eassumption. (* ...that filling lhs with plug is lhs' *)
        -- eassumption. (* ...that filling lhs with plug' is lhs'0 *)
        -- eassumption. (* ...that (MaximalOn lhs' n) *)
  - (* HoleSemicR *)
    sinvert Hf'. (* Invert hole-filling to show that ctx' = CtxSemic lhs'0 rhs *)
    sinvert Hn. (* Invert env(CtxSemic lhs' rhs): lhs' & rhs identically, PLUS EmptyOn rhs n \/ MaximalOn lhs' n *)
    constructor. (* Show a semicolon environment by showing lhs & rhs PLUS the above ^^ *)
    + clear IHHf. (* so we can see a damn thing *)
      apply env_typed_weakening_alt. (* Show (EnvTyped (env_union n n') rhs) by (EnvTyped n rhs) *)
      * assumption. (* no conflict *)
      * assumption. (* Already know that n is an environment typed for lhs *)
    + eapply IHHf; clear IHHf. (* Induction hypothesis where ctx' := rhs'0 *)
      * assumption. (* Already know that n and n' don't conflict *)
      * assumption. (* that n is an environment typed for rhs' *)
      * eassumption. (* ...that n' is an environment typed for plug' *)
      * assumption. (* ...n/n'/D/D' agree on maximality *)
      * assumption. (* ...n/n'/D/D' agree on emptiness *)
      * assumption. (* ...filling lhs with plug' is lhs'0 *)
    + clear IHHf. (* so we can see a damn thing *)
      destruct H5. (* We know that either rhs is empty on n or lhs'0 is maximal on it: case analysis *)
      * left. (* Empty case in H5 proves the empty case of the goal *)
        eapply agree_union. (* Prove (EmptyOn rhs'0 (env_union n n')) via assumptions & (EmptyOn rhs' n) *)
        -- eassumption. (* Already know that n and n' don't conflict *)
        -- eassumption. (* ...that n/n'/D/D' agree on emptiness *)
        -- eassumption. (* ...that filling rhs with plug is rhs' *)
        -- eassumption. (* ...that filling rhs with plug' is rhs'0 *)
        -- eassumption. (* ...that (EmptyOn rhs' n) *)
      * right. (* Maximal case in H5 proves the maximal case of the goal *)
        apply maximal_on_weakening_alt. (* We already know the left hand of union holds, so weaken away the right *)
        -- assumption. (* no conflict *)
        -- assumption. (* Already know that MaximalOn lhs n *)
Qed.
