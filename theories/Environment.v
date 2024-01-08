From Coq Require Import
  List.
From LambdaST Require Import
  Context
  Hole
  Ident
  Invert
  Prefix
  Terms
  Types.

Definition env : Set := ident -> option prefix.

Definition subst : ident -> prefix -> env -> env := fun id p n x => if eq_id id x then Some p else n x.
Arguments subst p n x/.
Definition union : env -> env -> env := fun n n' x => match n' x with None => n x | Some y => Some y end.
Arguments union n n' x/.

Definition MapsTo : prefix -> ident -> env -> Prop := fun p x n => n x = Some p.
Arguments MapsTo/ p x n. (* unfold immediately *)

Notation "n x |-> p" := (MapsTo p x n) (at level 98).

(* Theorem B.10, part I *)
Theorem maps_to_unique_literal : forall p x n,
  MapsTo p x n ->
  ~exists q, p <> q /\ MapsTo q x n.
Proof.
  intros p x n Hp [q [Hpq Hq]]. simpl in *. rewrite Hp in Hq. invert Hq. apply Hpq. reflexivity.
Qed.

Theorem maps_to_unique : forall p1 p2 x n,
  MapsTo p1 x n ->
  MapsTo p2 x n ->
  p1 = p2.
Proof. intros p1 p2 x n H1 H2. simpl in *. rewrite H1 in H2. invert H2. reflexivity. Qed.

(* Generalization of `emptyOn` and `maximalOn` from the paper *)
Definition prop_on_item : (prefix -> Prop) -> env -> ident -> Prop :=
  fun P n x => exists p, MapsTo p x n /\ P p.
Arguments prop_on_item P n x/.

Definition PropOn : (prefix -> Prop) -> context -> env -> Prop := fun P s n => Forall (prop_on_item P n) (vars_in s).
Arguments PropOn/ P s n.

Definition EmptyOn := PropOn Empty.
Arguments EmptyOn/ s n.

Definition MaximalOn := PropOn Maximal.
Arguments MaximalOn/ s n.

(* TODO: empty/maximal on (free variables in) terms *)

Definition Agree n n' D D' : Prop := (MaximalOn D n <-> MaximalOn D' n') /\ (EmptyOn D n <-> EmptyOn D' n').
Arguments Agree/ n n' D D'.

Inductive EnvTyped : env -> context -> Prop :=
  | EnvTyEmpty : forall n,
      EnvTyped n CtxEmpty
  | EnvTyHasTy : forall n p x s,
      MapsTo p x n ->
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

(* Theorem B.9 *)
Theorem maps_to_hole : forall n G D,
  EnvTyped n (fill G D) ->
  EnvTyped n D.
Proof.
  intros. remember (fill G D) as GD eqn:E. apply reflect_fill in E.
  generalize dependent G. generalize dependent D. induction H; intros; subst; simpl in *;
  invert E; try econstructor; try eassumption; try (eapply IHEnvTyped1; eassumption); eapply IHEnvTyped2; eassumption.
Qed.

(* Theorem B.10, part II *)
Theorem maps_to_has_type : forall n G x s,
  EnvTyped n (fill G (CtxHasTy x s)) ->
  exists p, (MapsTo p x n /\ PfxTyped p s).
Proof. intros. assert (A := maps_to_hole _ _ _ H). invert A. eexists. split; eassumption. Qed.

Lemma prop_on_item_weakening : forall P n n' vs,
  prop_on_item P n' vs ->
  prop_on_item P (union n n') vs.
Proof. intros P n n' vs [p [Hn' Hp]]. exists p. split; [| assumption]. simpl. rewrite Hn'. reflexivity. Qed.

Lemma env_typed_weakening : forall n n' G,
  EnvTyped n' G ->
  EnvTyped (union n n') G.
Proof.
  intros n n' G H. generalize dependent n.
  induction H; intros; econstructor;
  try apply IHEnvTyped1; try apply IHEnvTyped2;
  [simpl; rewrite H; reflexivity | assumption |].
  destruct H1; [left | right]; (eapply Forall_impl in H1; [apply H1 | apply prop_on_item_weakening]).
Qed.

Definition NoConflict (n n' : env) := forall x p,
  MapsTo p x n -> (n' x = None \/ MapsTo p x n').
Arguments NoConflict/ n n'.

Lemma env_typed_weakening_alt : forall n n' G,
  NoConflict n n' ->
  EnvTyped n G ->
  EnvTyped (union n n') G.
Proof.
  intros n n' G Hm Ht. generalize dependent n'.
  induction Ht; intros; simpl in *; econstructor; try apply IHHt1; try apply IHHt2; try eassumption.
  - simpl. specialize (Hm _ _ H) as [Hm | Hm]; rewrite Hm; [assumption | reflexivity].
  - destruct H; [left | right]; (eapply Forall_impl; [| eassumption]); intros; simpl in *;
    destruct H0 as [p [Hpn Hp]]; eexists; (split; [| eassumption]);
    (specialize (Hm _ _ Hpn) as [Hm | Hm]; rewrite Hm; [assumption | reflexivity]).
Qed.

Lemma agree_union : forall P n n' D D' lhs lhs' lhs'',
  NoConflict n n' ->
  (PropOn P D n <-> PropOn P D' n') ->
  FillWith D  lhs lhs'  ->
  FillWith D' lhs lhs'' ->
  PropOn P lhs' n ->
  PropOn P lhs'' (union n n').
Proof.
  intros P n n' D D' lhs lhs' lhs'' Hn Hp Hf Hf' H. generalize dependent P. generalize dependent n. generalize dependent n'.
  generalize dependent D'. generalize dependent lhs''. induction Hf; intros; invert Hf'; simpl in *; [
    apply Hp in H; eapply Forall_impl; [| eassumption]; intros a [p [Ha Hm]];
    eexists; split; [| eassumption]; simpl; rewrite Ha; reflexivity | | | |];
  apply Forall_app in H as [Hl Hr]; apply Forall_app; split; try (eapply IHHf; eassumption);
  (eapply Forall_impl; [| eassumption]); intros a [p [Ha Hm]]; eexists; (split; [| eassumption]);
  simpl; (specialize (Hn _ _ Ha) as [Hn | Hn]; rewrite Hn; [assumption | reflexivity]).
Qed.

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
  generalize dependent D'. generalize dependent GD'. induction E; intros; simpl in *.
  - invert E'. apply env_typed_weakening. assumption.
  - invert E'. invert Ht. econstructor. { eapply IHE; eassumption. }
    (* NOTE: this is where the extra assumption becomes necessary, since the wrong side of `union` is weakened *)
    apply env_typed_weakening_alt; assumption.
  - invert E'. invert Ht. constructor. { apply env_typed_weakening_alt; assumption. } eapply IHE; eassumption.
  - invert E'. invert Ht. constructor; [eapply IHE | apply env_typed_weakening_alt |]; try eassumption. destruct H5.
    + left. eapply Forall_impl; [| eassumption]. intros a [p [Ha Hp]]. simpl in *. eexists. split; [| eassumption].
      specialize (Hn _ _ Ha) as [Hn | Hn]; rewrite Hn; [assumption | reflexivity].
    + right. clear IHE. eapply agree_union; eassumption.
  - invert E'. invert Ht. constructor. { apply env_typed_weakening_alt; assumption. } { eapply IHE; eassumption. }
    clear IHE. destruct H5; [left | right]. { eapply agree_union; eassumption. } eapply Forall_impl; [| eassumption].
    intros a [p [Ha Hp]]. eexists. split; [| eassumption]. simpl.
    specialize (Hn _ _ Ha) as [Hn | Hn]; rewrite Hn; [assumption | reflexivity].
Qed.
