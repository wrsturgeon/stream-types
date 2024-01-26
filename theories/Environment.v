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

Definition MapsTo (p : prefix) (x : ident) (n : env) : Prop := n x = Some p.
Arguments MapsTo/ p x n. (* unfold immediately *)

Notation "n x |-> p" := (MapsTo p x n) (at level 98).

(* Theorem B.10, part I *)
Theorem maps_to_unique_literal : forall p x n,
  MapsTo p x n ->
  ~exists q, p <> q /\ MapsTo q x n.
Proof. sfirstorder. Qed.

Theorem maps_to_unique : forall p1 p2 x n,
  MapsTo p1 x n ->
  MapsTo p2 x n ->
  p1 = p2.
Proof. sfirstorder. Qed.

(* Generalization of `emptyOn` and `maximalOn` from the paper *)
Definition PropOnItem (P : prefix -> Prop) (n : env) (x : ident) : Prop :=
  exists p, MapsTo p x n /\ P p.
Arguments PropOnItem P n x/.

Definition PropOn (P : prefix -> Prop) (s : set ident) (n : env) : Prop := forall x, s x -> PropOnItem P n x.
Arguments PropOn/ P s n.

Definition EmptyOn := PropOn EmptyPrefix.
Arguments EmptyOn/ s n.

Definition MaximalOn := PropOn MaximalPrefix.
Arguments MaximalOn/ s n.

Theorem prop_on_restrict : forall P s s' n,
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
  exists p, (MapsTo p x n /\ PfxTyped p s).
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
  s x -> MapsTo p x n -> (n' x = None \/ MapsTo p x n').
Arguments NoConflictOn/ s n n'.

Theorem no_conflict_restrict : forall s s' n n',
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

Theorem disjoint_noconflict : forall s n n',
  Disjoint (set_intersection s (dom n)) (set_intersection s (dom n')) ->
  NoConflictOn s n n'.
Proof.
  unfold NoConflictOn in *; intros s n n' H x. remember (n' x) as n'x; destruct n'x. sfirstorder. sfirstorder.
Qed.

Lemma env_typed_weakening_alt : forall n n' G,
  NoConflictOn (fv G) n n' ->
  EnvTyped n G ->
  EnvTyped (env_union n n') G.
Proof.
  intros n n' G Hm Ht. generalize dependent n'.
  (* induction Ht; intros; simpl in *; econstructor; try apply IHHt1; try apply IHHt2; try eassumption. *)
  (* hauto l: on. *)
  (* destruct H; [left | right]; hauto drew: off. *)
Admitted.

Lemma prop_on_union_fill : forall P n n' d d' h hd hd',
  NoConflictOn (fv h) n n' ->
  (PropOn P (fv d) n <-> PropOn P (fv d') n') ->
  FillWith d  h hd  ->
  FillWith d' h hd' ->
  PropOn P (fv hd) n ->
  PropOn P (fv hd') (env_union n n').
Proof.
  (* intros P n n' D D' lhs lhs' lhs'' Hn Hp Hf Hf' H. generalize dependent P. generalize dependent n. generalize dependent n'.
  generalize dependent D'. generalize dependent lhs''.
  induction Hf; intros; sinvert Hf'; simpl in *; [ apply Hp in H; eapply Forall_impl; [|eauto]; hauto q:on | | | |];
  apply Forall_app in H as [Hl Hr]; apply Forall_app; split; try (eapply IHHf; eassumption);
  (eapply Forall_impl; [| eassumption]); intros a [p [Ha Hm]]; eexists; (split; [| eassumption]);
  simpl; (specialize (Hn _ _ Ha) as [Hn | Hn]; rewrite Hn; [assumption | reflexivity]).
Qed.  *)
Admitted.

Theorem fill_replace : forall h d d' n n',
  NoConflictOn (fv h) n n' ->
  EnvTyped n (fill h d) ->
  EnvTyped n' d' ->
  Agree n n' d d' ->
  EnvTyped (env_union n n') (fill h d').
Proof.
  intros h d d' n n' Hnc Ht Ht' [Hm He].
  remember (fill h d) as hd eqn:E. apply reflect_fill in E.
  remember (fill h d') as hd' eqn:E'. apply reflect_fill in E'. generalize dependent n. generalize dependent n'.
  generalize dependent d'. generalize dependent hd'.
  induction E; intros.
  - sauto lq: on use: env_typed_weakening.
  - sinvert E'. constructor.
    + eapply IHE. eauto. eauto. eapply no_conflict_restrict; [|eauto]; sfirstorder.
      sauto lq: on. sfirstorder. sfirstorder.
    + sauto q: on use:env_typed_weakening_alt.
  - sinvert E'. constructor.
    + sauto q: on use:env_typed_weakening_alt.
    + eapply IHE. eauto. eauto. eapply no_conflict_restrict; [|eauto]; sfirstorder.
      sauto lq: on. sfirstorder. sfirstorder.
  - sinvert E'. constructor.
    + eapply IHE. eauto. eauto. eapply no_conflict_restrict; [|eauto]; sfirstorder.
      sauto lq: on. sfirstorder. sfirstorder.
    + sauto q: on use:env_typed_weakening_alt.
    + sinvert Ht. destruct H5; [left | right]; admit.
  - admit.
Admitted.

(* Theorem B.11
Theorem agree_typed : forall n n' G D D',
  NoConflictOn n n' ->
  EnvTyped n (fill G D) ->
  EnvTyped n' D' ->
  Agree n n' D D' ->
  EnvTyped (union n n') (fill G D').
Proof.
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
Qed. *)

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
  + eapply env_typed_weakening_alt; [|eauto]. sauto lq: on rew: off use: disjoint_noconflict. 
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
  + eapply env_typed_weakening_alt; [|eauto]. sauto lq: on rew: off use: disjoint_noconflict. 
  + sfirstorder use: env_typed_weakening.
  + destruct H2; [left | right]; hfcrush.
Qed.
