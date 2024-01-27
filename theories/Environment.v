From Coq Require Import
  List.
From LambdaST Require Import
  Context
  FV
  Hole
  Ident
  Prefix
  Terms
  Types.
From Hammer Require Import
  Tactics.

Definition env : Set := ident -> option prefix.

Definition dom (n : env) : set ident :=
  fun x => exists p, n x = Some p.

Definition env_union (n n' : env) : env := fun x =>
  match n' x with
  | None => n x
  | Some y => Some y
  end.
Arguments env_union n n' x/.

Definition singleton_env (id : ident) (p : prefix) : env := fun x =>
  if eq_id id x then Some p else None.
Arguments singleton_env id p x/.

Definition subst (x : ident) (p : prefix) (rho : env) : env :=
  env_union rho (singleton_env x p).
Arguments subst x p rho x/.

(* Theorem B.10, part I *)
Theorem maps_to_unique_literal : forall p x (n : env),
  n x = Some p ->
  ~exists q, p <> q /\ n x = Some q.
Proof. sfirstorder. Qed.

Theorem maps_to_unique : forall p1 p2 x (n : env),
  n x = Some p1 ->
  n x = Some p2 ->
  p1 = p2.
Proof. sfirstorder. Qed.

(* Generalization of `emptyOn` and `maximalOn` from the paper *)
Definition PropOnItem (P : prefix -> Prop) (n : env) (x : ident) : Prop :=
  exists p, n x = Some p /\ P p.
Arguments PropOnItem P n x/.

Definition PropOn (P : prefix -> Prop) (s : set ident) (n : env) : Prop := forall x, s x -> PropOnItem P n x.
Arguments PropOn/ P s n.

Definition EmptyOn := PropOn EmptyPrefix.
Arguments EmptyOn/ s n.

Definition MaximalOn := PropOn MaximalPrefix.
Arguments MaximalOn/ s n.

Theorem prop_on_contains : forall P s s' n,
  Contains s s' ->
  PropOn P s' n ->
  PropOn P s n.
Proof. sfirstorder. Qed.

Definition Agree n n' (D : context) (D' : context) : Prop :=
  (MaximalOn (fv D) n <-> MaximalOn (fv D') n') /\ (EmptyOn (fv D) n <-> EmptyOn (fv D') n').
Arguments Agree/ n n' D D'.

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
      (EmptyOn (fv D) n \/ MaximalOn (fv G) n) ->
      EnvTyped n (CtxSemic G D)
  .

(* Theorem B.9 *)
Theorem maps_to_hole : forall n G D,
  EnvTyped n (fill G D) ->
  EnvTyped n D.
Proof.
  intros. remember (fill G D) as GD eqn:E. apply reflect_fill in E.
  generalize dependent G. generalize dependent D. induction H; intros; subst; simpl in *;
  sinvert E; try econstructor; try eassumption; try (eapply IHEnvTyped1; eassumption); eapply IHEnvTyped2; eassumption.
Qed.

(* Theorem B.10, part II *)
Theorem maps_to_has_type : forall n G x s,
  EnvTyped n (fill G (CtxHasTy x s)) ->
  exists p, (n x = Some p /\ PfxTyped p s).
Proof. intros. assert (A := maps_to_hole _ _ _ H). sinvert A. eexists. split; eassumption. Qed.

Lemma prop_on_item_weakening : forall P n n' vs,
  PropOnItem P n' vs ->
  PropOnItem P (env_union n n') vs.
Proof. intros P n n' vs [p [Hn' Hp]]. exists p. split; [| assumption]. simpl. rewrite Hn'. reflexivity. Qed.

Lemma env_typed_weakening : forall n n' G,
  EnvTyped n' G ->
  EnvTyped (env_union n n') G.
Proof.
  intros n n' G H. generalize dependent n.
  induction H; intros; econstructor; hauto lq: on.
Qed.

Definition NoConflictOn (s : set ident) (n n' : env) := forall x p,
  s x -> n x = Some p -> (n' x = None \/ n' x = Some p).
Arguments NoConflictOn/ s n n'.

Theorem no_conflict_contains : forall s s' n n',
  Contains s s' ->
  NoConflictOn s' n n' ->
  NoConflictOn s n n'.
Proof. hauto lq:on. Qed.

Theorem no_conflict_sym : forall s n n', NoConflictOn s n n' -> NoConflictOn s n' n.
Proof.
  unfold NoConflictOn in *; intros.
  remember (n x) as nx.
  destruct nx.
  - hauto drew: off.
  - sfirstorder.
Qed.

Theorem disjoint_no_conflict : forall s n n',
  Disjoint (set_intersection s (dom n)) (set_intersection s (dom n')) ->
  NoConflictOn s n n'.
Proof. simpl. intros. destruct (n' x) eqn:E; sfirstorder. Qed.

Lemma env_typed_weakening_alt : forall n n' G,
  NoConflictOn (fv G (* fun _ => True *)) n n' ->
  EnvTyped n G ->
  EnvTyped (env_union n n') G.
Proof.
  intros n n' G Hc Ht. generalize dependent n'. induction Ht; intros; simpl in *. { constructor. }
  - sauto.
  - sauto lq: on.
  - constructor. { hauto l: on. } { hauto l: on. } destruct H; simpl in *. { hauto lq: on. } qauto l: on.
Qed.

(* Theorem B.11 *)
Theorem agree_typed : forall n n' G D D',
  EnvTyped n (fill G D) ->
  EnvTyped n' D' ->
  Agree n n' D D' ->
  EnvTyped (env_union n n') (fill G D').
Proof.
  cbn. intros n n' G D D' Ht Ht' [Ham Hae]. remember (fill G D) as GD eqn:E. apply reflect_fill in E.
  generalize dependent n. generalize dependent n'. generalize dependent D'. induction E; intros; cbn in *.
  - (* We have an assumption that this holds for the right side of the union, so weaken away the left. *)
    apply env_typed_weakening. assumption.
(*
  intros n n' G D D' Hn Ht Ht' [Hm He]. remember (fill G D) as GD eqn:E. apply reflect_fill in E.
  remember (fill G D') as GD' eqn:E'. apply reflect_fill in E'. generalize dependent n. generalize dependent n'.
  generalize dependent D'. generalize dependent GD'. induction E; intros; simpl in *.
  - sauto lq: on use:env_typed_weakening.
  - sauto lq: on use:env_typed_weakening_alt.
  - sauto use: env_typed_weakening_alt.
  - sinvert E'. sinvert Ht. constructor.
    + hauto lq: on.
    + hauto l: on use:env_typed_weakening_alt.
    + destruct H5.
      * left. hauto qb: on drew: off.
      * right. qauto l: on use: prop_on_union.
  - sinvert E'. sinvert Ht. constructor; [hauto l: on use:env_typed_weakening_alt | qauto l: on use:env_typed_weakening_alt|].
    clear IHE.
    destruct H5; [left | right]. qauto l: on use: prop_on_union. hauto qb: on drew: off.
Qed.
*)
Admitted.

(* environment typing smart constructors *)
Theorem env_typed_singleton : forall x s p,
  PfxTyped p s ->
  EnvTyped (singleton_env x p) (CtxHasTy x s).
Proof.
  intros; econstructor; [| eauto]; cbn.
  unfold singleton_env.
  hauto lq: on use: eq_id_refl.
Qed.

Theorem env_typed_comma: forall n n' g g',
  Disjoint (dom n) (dom n') ->
  EnvTyped n g ->
  EnvTyped n' g' ->
  EnvTyped (env_union n n') (CtxComma g g').
Proof.
  intros.
  constructor.
  + eapply env_typed_weakening_alt; [|eauto]. sauto lq: on rew: off use: disjoint_no_conflict.
  + sfirstorder use: env_typed_weakening.
Qed.

Theorem env_typed_semic : forall n n' g g',
  Disjoint (dom n) (dom n') ->
  EnvTyped n g ->
  EnvTyped n' g' ->
  EmptyOn (fv g') n' \/ MaximalOn (fv g) n ->
  EnvTyped (env_union n n') (CtxSemic g g').
Proof.
  intros.
  constructor.
  + eapply env_typed_weakening_alt; [|eauto]. sauto lq: on rew: off use: disjoint_no_conflict.
  + sfirstorder use: env_typed_weakening.
  + destruct H2; [left | right]; hfcrush.
Qed.
