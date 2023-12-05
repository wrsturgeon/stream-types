From Coq Require Import
  List.
From LambdaST Require Import
  Context
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
  Contains D G ->
  EnvTyped n G ->
  EnvTyped n D.
Proof.
  intros n G D Hc Ht. generalize dependent n.
  induction Hc; intros; try (invert Ht; apply IHHc); assumption.
Qed.

(* Theorem B.10, part II *)
Theorem maps_to_has_type : forall n G x s,
  Contains (CtxHasTy x s) G ->
  EnvTyped n G ->
  exists p, (MapsTo p x n /\ PfxTyped p s).
Proof.
  intros n G x s Hx Ht. generalize dependent x. generalize dependent s.
  induction Ht; intros; invert Hx; try (apply IHHt1; assumption); try (apply IHHt2; assumption).
  exists p. split; assumption.
Qed.

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

(* Theorem B.11 *)
Theorem agree_union : forall n n' G G' D D',
  FindReplace D D' G G' ->
  EnvTyped n G ->
  EnvTyped n' D' ->
  Agree n n' D D' ->
  EnvTyped (union n n') G'.
Proof.
  intros n n' G G' D D' Hhole Hn Hn' [HAm HAe].
  generalize dependent n. generalize dependent n'.
  induction Hhole; intros.
  - apply env_typed_weakening. assumption.
  - invert Hn. constructor.
    + apply IHHhole; assumption.
    + Abort.
