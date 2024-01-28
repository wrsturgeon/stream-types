From Coq Require Import
  List
  String.
From LambdaST Require Import
  Context
  Hole
  Prefix
  Terms
  Types.
From Hammer Require Import
  Tactics.

Definition env : Set := string -> option prefix.
Hint Unfold env : core.

Definition subst : string -> prefix -> env -> env := fun id p n x => if eqb id x then Some p else n x.
Arguments subst p n x/.
Hint Unfold subst : core.

Definition union : env -> env -> env := fun n n' x => match n' x with None => n x | Some y => Some y end.
Arguments union n n' x/.
Hint Unfold union : core.

(* Theorem B.10, part I *)
Theorem maps_to_unique_literal : forall p x (n : env),
  n x = Some p ->
  ~exists q, p <> q /\ n x = Some q.
Proof.
  intros p x n Hp [q [Hpq Hq]]. cbn in *. rewrite Hp in Hq. sinvert Hq. apply Hpq. reflexivity.
Qed.
Hint Resolve maps_to_unique_literal : core.

Theorem maps_to_unique : forall p1 p2 x (n : env),
  n x = Some p1 ->
  n x = Some p2 ->
  p1 = p2.
Proof. intros p1 p2 x n H1 H2. cbn in *. rewrite H1 in H2. sinvert H2. reflexivity. Qed.
Hint Resolve maps_to_unique : core.

(* Generalization of `emptyOn` and `maximalOn` from the paper *)
Definition prop_on_item : (prefix -> Prop) -> env -> string -> Prop :=
  fun P n x => exists p, n x = Some p /\ P p.
Arguments prop_on_item P n x/.
Hint Unfold prop_on_item : core.

Definition PropOn : (prefix -> Prop) -> context -> env -> Prop := fun P s n => Forall (prop_on_item P n) (vars_in s).
Arguments PropOn/ P s n.
Hint Unfold PropOn : core.

Definition EmptyOn := PropOn Empty.
Arguments EmptyOn/ s n.
Hint Unfold EmptyOn : core.

Definition MaximalOn := PropOn Maximal.
Arguments MaximalOn/ s n.
Hint Unfold MaximalOn : core.

(* TODO: empty/maximal on (free variables in) terms *)

Definition Agree n n' D D' : Prop := (MaximalOn D n <-> MaximalOn D' n') /\ (EmptyOn D n <-> EmptyOn D' n').
Arguments Agree/ n n' D D'.
Hint Unfold Agree : core.

Inductive EnvTyped : env -> context -> Prop :=
  | EnvTyEmpty : forall n,
      EnvTyped n CtxEmpty
  | EnvTyHasTy : forall n p x s,
      n x = Some p ->
      PfxTyped p s ->
      EnvTyped n (CtxHasTy x s)
  | EnvTyComma : forall n G D,
      EnvTyped n G ->
      EnvTyped n D ->
      EnvTyped n (CtxComma G D)
  | EnvTySemic : forall n G D,
      EnvTyped n G ->
      EnvTyped n D ->
      (EmptyOn D n \/ MaximalOn G n) ->
      EnvTyped n (CtxSemic G D)
  .
Hint Constructors EnvTyped : core.

(* Theorem B.9 *)
Theorem maps_to_hole : forall n G D,
  EnvTyped n (fill G D) ->
  EnvTyped n D.
Proof.
  intros. remember (fill G D) as GD eqn:E. apply reflect_fill in E.
  generalize dependent G. generalize dependent D. induction H; intros; subst; cbn in *;
  sinvert E; try econstructor; try eassumption; try (eapply IHEnvTyped1; eassumption); eapply IHEnvTyped2; eassumption.
Qed.
Hint Resolve maps_to_hole : core.

(* Theorem B.10, part II *)
Theorem maps_to_has_type : forall n G x s,
  EnvTyped n (fill G (CtxHasTy x s)) ->
  exists p, (n x = Some p /\ PfxTyped p s).
Proof. intros. assert (A := maps_to_hole _ _ _ H). sinvert A. eexists. split; eassumption. Qed.
Hint Resolve maps_to_has_type : core.

Lemma prop_on_item_weakening : forall P n n' vs,
  prop_on_item P n' vs ->
  prop_on_item P (union n n') vs.
Proof. intros P n n' vs [p [Hn' Hp]]. exists p. split; [| assumption]. cbn. rewrite Hn'. reflexivity. Qed.
Hint Resolve prop_on_item_weakening : core.

Lemma env_typed_weakening : forall n n' G,
  EnvTyped n' G ->
  EnvTyped (union n n') G.
Proof.
  intros n n' G H. generalize dependent n.
  induction H; intros; econstructor;
  try apply IHEnvTyped1; try apply IHEnvTyped2;
  [cbn; rewrite H; reflexivity | assumption |].
  destruct H1; [left | right]; (eapply Forall_impl in H1; [apply H1 | apply prop_on_item_weakening]).
Qed.
Hint Resolve env_typed_weakening : core.

Definition NoConflict (n n' : env) := forall x p,
  n x = Some p -> (n' x = None \/ n' x = Some p).
Arguments NoConflict/ n n'.
Hint Unfold NoConflict : core.

Lemma env_typed_weakening_alt : forall n n' G,
  NoConflict n n' ->
  EnvTyped n G ->
  EnvTyped (union n n') G.
Proof.
  intros n n' G Hm Ht. generalize dependent n'.
  induction Ht; intros; cbn in *; econstructor; try apply IHHt1; try apply IHHt2; try eassumption.
  - cbn. specialize (Hm _ _ H) as [Hm | Hm]; rewrite Hm; [assumption | reflexivity].
  - destruct H; [left | right]; (eapply Forall_impl; [| eassumption]); intros; cbn in *;
    destruct H0 as [p [Hpn Hp]]; eexists; (split; [| eassumption]);
    (specialize (Hm _ _ Hpn) as [Hm | Hm]; rewrite Hm; [assumption | reflexivity]).
Qed.
Hint Resolve env_typed_weakening_alt : core.

Lemma agree_union : forall P n n' D D' lhs lhs' lhs'',
  NoConflict n n' ->
  (PropOn P D n <-> PropOn P D' n') ->
  FillWith D  lhs lhs'  ->
  FillWith D' lhs lhs'' ->
  PropOn P lhs' n ->
  PropOn P lhs'' (union n n').
Proof.
  intros P n n' D D' lhs lhs' lhs'' Hn Hp Hf Hf' H. generalize dependent P. generalize dependent n. generalize dependent n'.
  generalize dependent D'. generalize dependent lhs''. induction Hf; intros; sinvert Hf'; cbn in *; [
    apply Hp in H; eapply Forall_impl; [| eassumption]; intros a [p [Ha Hm]];
    eexists; split; [| eassumption]; cbn; rewrite Ha; reflexivity | | | |];
  apply Forall_app in H as [Hl Hr]; apply Forall_app; split; try (eapply IHHf; eassumption);
  (eapply Forall_impl; [| eassumption]); intros a [p [Ha Hm]]; eexists; (split; [| eassumption]);
  cbn; (specialize (Hn _ _ Ha) as [Hn | Hn]; rewrite Hn; [assumption | reflexivity]).
Qed.
Hint Resolve agree_union : core.

(* Theorem B.11 *)
Theorem agree_typed : forall n n' G D D',
  NoConflict n n' ->
  EnvTyped n (fill G D) ->
  EnvTyped n' D' ->
  Agree n n' D D' ->
  EnvTyped (union n n') (fill G D').
Proof.
  intros n n' G D D' Hn Ht Ht' [Hm He]. remember (fill G D) as GD eqn:E. apply reflect_fill in E.
  remember (fill G D') as GD' eqn:E'. apply reflect_fill in E'. generalize dependent n. generalize dependent n'.
  generalize dependent D'. generalize dependent GD'. induction E; intros; cbn in *.
  - sinvert E'. apply env_typed_weakening. assumption.
  - sinvert E'. sinvert Ht. econstructor. { eapply IHE; eassumption. }
    (* NOTE: this is where the extra assumption becomes necessary, since the wrong side of `union` is weakened *)
    apply env_typed_weakening_alt; assumption.
  - sinvert E'. sinvert Ht. constructor. { apply env_typed_weakening_alt; assumption. } eapply IHE; eassumption.
  - sinvert E'. sinvert Ht. constructor; [eapply IHE | apply env_typed_weakening_alt |]; try eassumption. destruct H5.
    + left. eapply Forall_impl; [| eassumption]. intros a [p [Ha Hp]]. cbn in *. eexists. split; [| eassumption].
      specialize (Hn _ _ Ha) as [Hn | Hn]; rewrite Hn; [assumption | reflexivity].
    + right. clear IHE. eapply agree_union; eassumption.
  - sinvert E'. sinvert Ht. constructor. { apply env_typed_weakening_alt; assumption. } { eapply IHE; eassumption. }
    clear IHE. destruct H5; [left | right]. { eapply agree_union; eassumption. } eapply Forall_impl; [| eassumption].
    intros a [p [Ha Hp]]. eexists. split; [| eassumption]. cbn.
    specialize (Hn _ _ Ha) as [Hn | Hn]; rewrite Hn; [assumption | reflexivity].
Qed.
Hint Resolve agree_typed : core.
