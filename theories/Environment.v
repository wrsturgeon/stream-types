From Coq Require Import
  List.
From LambdaST Require Import
  Context
  Hole
  Ident
  Invert
  Prefix
  Terms
  FV
  Types.

From Hammer Require Import Tactics.

Definition env : Set := ident -> option prefix.

Definition union : env -> env -> env := fun n n' x => match n' x with None => n x | Some y => Some y end.
Arguments union n n' x/.

Definition singleton_env : ident -> prefix -> env :=
  fun id p x => if eq_id id x then Some p else None.

Definition subst : ident -> prefix -> env -> env :=
  fun x p rho => union rho (singleton_env x p).
Arguments subst p n x/.

Definition MapsTo : prefix -> ident -> env -> Prop := fun p x n => n x = Some p.
Arguments MapsTo/ p x n. (* unfold immediately *)

Notation "n x |-> p" := (MapsTo p x n) (at level 98).

(* Theorem B.10, part I *)
Theorem maps_to_unique_literal : forall p x n,
  MapsTo p x n ->
  ~exists q, p <> q /\ MapsTo q x n.
Proof.
sfirstorder.
Qed.

Theorem maps_to_unique : forall p1 p2 x n,
  MapsTo p1 x n ->
  MapsTo p2 x n ->
  p1 = p2.
Proof. sfirstorder. Qed.

(* Generalization of `emptyOn` and `maximalOn` from the paper *)
Definition prop_on_item : (prefix -> Prop) -> env -> ident -> Prop :=
  fun P n x => exists p, MapsTo p x n /\ P p.
Arguments prop_on_item P n x/.

Definition PropOn : (prefix -> Prop) -> context -> env -> Prop := fun P G n => forall x, fv G x -> prop_on_item P n x.
Arguments PropOn/ P G n.

Definition EmptyOn := PropOn Empty.
Arguments EmptyOn/ G n.

Definition MaximalOn := PropOn Maximal.
Arguments MaximalOn/ G n.

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
  induction H; intros; econstructor; hauto lq: on.
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
  hauto l: on.
  destruct H; [left | right]; hauto drew: off.
Qed.
(* 
Lemma agree_union : forall P n n' D D' lhs lhs' lhs'',
  NoConflict n n' ->
  (PropOn P D n <-> PropOn P D' n') ->
  FillWith D  lhs lhs'  ->
  FillWith D' lhs lhs'' ->
  PropOn P lhs' n ->
  PropOn P lhs'' (union n n').
Proof.
  intros P n n' D D' lhs lhs' lhs'' Hn Hp Hf Hf' H. generalize dependent P. generalize dependent n. generalize dependent n'.
  generalize dependent D'. generalize dependent lhs''.
  induction Hf; intros; sinvert Hf'; simpl in *; [ apply Hp in H; eapply Forall_impl; [|eauto]; hauto q:on | | | |];
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
  - sauto lq: on use:env_typed_weakening.
  - sauto lq: on use:env_typed_weakening_alt.
  - sauto use: env_typed_weakening_alt.
  - sinvert E'. sinvert Ht. constructor.
    + sfirstorder.
    + sfirstorder use:env_typed_weakening_alt.
    + destruct H5.
      * left. eapply Forall_impl; [| eauto]. hauto drew: off.
      * right. qauto l: on use: agree_union.
  - sinvert E'. sinvert Ht. constructor; [hauto l: on use:env_typed_weakening_alt | qauto l: on use:env_typed_weakening_alt|].
    clear IHE.
    destruct H5; [left | right]. qauto l: on use: agree_union. eapply Forall_impl; [| eauto].
    hauto drew: off.
Qed. *)
