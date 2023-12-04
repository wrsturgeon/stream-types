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

Definition MapsTo : prefix -> ident -> env -> Prop := fun p x n => n x = Some p.
Arguments MapsTo/ p x n. (* unfold immediately *)

Notation "n x |-> p" := (MapsTo p x n) (at level 98).

(* Theorem B.10, part I *)
Theorem maps_to_unique : forall p x n, MapsTo p x n -> ~exists q, p <> q /\ MapsTo q x n.
Proof.
  intros p x n Hp [q [Hpq Hq]]. simpl in *. rewrite Hp in Hq. invert Hq. apply Hpq. reflexivity.
Qed.

Definition EmptyOn : context -> env -> Prop := fun s n =>
  Forall (fun x => exists p, (MapsTo p x n) /\ Empty p) (vars_in s).

Definition MaximalOn : context -> env -> Prop := fun s n =>
  Forall (fun x => exists p, (MapsTo p x n) /\ Maximal p) (vars_in s).

(* TODO: empty/maximal on (free variables in) terms *)

(* NOTE: This definition is almost certainly wrong in the paper. *)
Definition Agree n n' D D' : Prop := (MaximalOn D n <-> MaximalOn D' n') /\ (EmptyOn D n <-> MaximalOn D' n').

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

(*
(* Theorem B.11 *)
Theorem agree_dot : forall n n' G G' D D',
  FindReplace D D' G G' ->
  EnvTyped n G ->
  EnvTyped n' D' ->
  Agree n n' D D' ->
  EnvTyped not_sure G'.
*)
