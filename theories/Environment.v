From Coq Require Import
  List
  String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  FV
  Hole
  Prefix
  Sets
  Terms
  Types.

Definition env : Set := string -> option prefix.
Hint Unfold env : core.

Definition dom (n : env) : set string :=
  fun x => exists p, n x = Some p.
Arguments dom n x/.
Hint Unfold dom : core.

Definition env_union (n n' : env) : env := fun x =>
  match n' x with
  | None => n x
  | Some y => Some y
  end.
Arguments env_union n n' x/.
Hint Unfold env_union : core.

Definition env_drop (n : env) (x : string) : env := fun y =>
  if eqb x y then None else n x.

Definition singleton_env (id : string) (p : prefix) : env := fun x =>
  if eqb id x then Some p else None.
Arguments singleton_env id p x/.
Hint Unfold singleton_env : core.

Definition env_subst (x : string) (p : prefix) (rho : env) : env :=
  env_union rho (singleton_env x p).
Arguments env_subst x p rho x/.
Hint Unfold env_subst : core.

(* Theorem B.10, part I *)
Theorem maps_to_unique_literal : forall p x (n : env),
  n x = Some p ->
  ~exists q, p <> q /\ n x = Some q.
Proof. sfirstorder. Qed.
Hint Resolve maps_to_unique_literal : core.

Theorem maps_to_unique : forall p1 p2 x (n : env),
  n x = Some p1 ->
  n x = Some p2 ->
  p1 = p2.
Proof. sfirstorder. Qed.
Hint Resolve maps_to_unique : core.

(* Generalization of `emptyOn` and `maximalOn` from the paper *)
Definition PropOnItem (P : prefix -> Prop) (n : env) (x : string) : Prop :=
  exists p, n x = Some p /\ P p.
Arguments PropOnItem P n x/.
Hint Unfold PropOnItem : core.

Definition PropOn (P : prefix -> Prop) (s : set string) (n : env) : Prop := forall x, s x -> PropOnItem P n x.
Arguments PropOn/ P s n.
Hint Unfold PropOn : core.

Definition EmptyOn := PropOn EmptyPrefix.
Arguments EmptyOn/ s n.
Hint Unfold EmptyOn : core.

Definition MaximalOn := PropOn MaximalPrefix.
Arguments MaximalOn/ s n.
Hint Unfold MaximalOn : core.

Theorem prop_on_contains : forall P s s' n,
  SubsetOf s' s ->
  PropOn P s' n ->
  PropOn P s n.
Proof. sfirstorder. Qed.

Theorem prop_on_union: forall P s s' n,
  PropOn P (set_union s s') n <-> PropOn P s n /\ PropOn P s' n.
Proof.
sfirstorder.
Qed.


Definition Agree (n n' : env) (D D' : context) : Prop :=
  (MaximalOn (fv D) n <-> MaximalOn (fv D') n') /\
  (EmptyOn (fv D) n <-> EmptyOn (fv D') n').
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
      (EmptyOn (fv D) n \/ MaximalOn (fv G) n) ->
      EnvTyped n (CtxSemic G D)
  .
Hint Constructors EnvTyped : core.

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

Definition NoConflict (n n' : env) := forall x p,
  n x = Some p ->
  forall p',
  n' x = Some p' ->
  p = p'.
Arguments NoConflict/ n n'.
Hint Unfold NoConflict : core.

Lemma prop_on_fill : forall P n d d' g lhs lhs',
  FillWith d g lhs ->
  FillWith d' g lhs' ->
  PropOn P (fv d') n ->
  PropOn P (fv lhs) n ->
  PropOn P (fv lhs') n.
Proof.
  cbn in *. intros P n d d' g lhs lhs' Hf Hf' Hp' Hp x Hfv.
  assert (A' : SetEq (fv lhs') (set_union (fv d') (fv g))). { apply fv_fill. assumption. } apply A' in Hfv.
  assert (A : SetEq (fv lhs) (set_union (fv d) (fv g))). { apply fv_fill. assumption. } cbn in *.
  destruct Hfv. 2: { apply Hp. apply A. right. assumption. } apply Hp'. assumption.
Qed.
Hint Resolve prop_on_fill : core.

Lemma prop_on_item_weakening : forall P nr nl vs,
  PropOnItem P nr vs ->
  PropOnItem P (env_union nl nr) vs.
Proof. intros P nl nr vs [p [Hn' Hp]]. exists p. split; [| assumption]. cbn. rewrite Hn'. reflexivity. Qed.
Hint Resolve prop_on_item_weakening : core.

Lemma prop_on_weakening : forall P nr nl ctx,
  PropOn P ctx nr ->
  PropOn P ctx (env_union nl nr).
Proof. sfirstorder use:prop_on_item_weakening. Qed.
Hint Resolve prop_on_weakening : core.

Lemma empty_on_weakening : forall nr nl ctx,
  EmptyOn ctx nr ->
  EmptyOn ctx (env_union nl nr).
Proof. apply prop_on_weakening. Qed.
Hint Resolve empty_on_weakening : core.

Lemma maximal_on_weakening : forall nr nl ctx,
  MaximalOn ctx nr ->
  MaximalOn ctx (env_union nl nr).
Proof. apply prop_on_weakening. Qed.
Hint Resolve maximal_on_weakening : core.

Lemma env_typed_weakening : forall n n' G,
  EnvTyped n' G ->
  EnvTyped (env_union n n') G.
Proof.
  intros n n' G H. generalize dependent n.
  induction H; intros; econstructor;
  try apply IHEnvTyped1; try apply IHEnvTyped2;
  [cbn; rewrite H; reflexivity | assumption |].
  destruct H1; [left | right]; apply prop_on_weakening; assumption.
Qed.
Hint Resolve env_typed_weakening : core.

Theorem prop_on_item_weakening_alt : forall P nl nr vs,
  NoConflict nl nr ->
  PropOnItem P nl vs ->
  PropOnItem P (env_union nl nr) vs.
Proof.
  cbn. intros P nl nr vs H [p [H1 H2]]. rewrite H1.
  destruct (nr vs) eqn:E; eexists; (split; [reflexivity | hauto l: on]).
Qed.
Hint Resolve prop_on_item_weakening_alt : core.

Lemma prop_on_weakening_alt : forall P nl nr ctx,
  NoConflict nl nr ->
  PropOn P ctx nl ->
  PropOn P ctx (env_union nl nr).
Proof. sfirstorder use: prop_on_item_weakening_alt. Qed.
Hint Resolve prop_on_weakening_alt : core.

Lemma empty_on_weakening_alt : forall nl nr ctx,
  NoConflict nl nr ->
  EmptyOn ctx nl ->
  EmptyOn ctx (env_union nl nr).
Proof. apply prop_on_weakening_alt. Qed.
Hint Resolve empty_on_weakening_alt : core.

Lemma maximal_on_weakening_alt : forall nl nr ctx,
  NoConflict nl nr ->
  MaximalOn ctx nl ->
  MaximalOn ctx (env_union nl nr).
Proof. apply prop_on_weakening_alt. Qed.
Hint Resolve maximal_on_weakening_alt : core.

Lemma env_typed_weakening_alt : forall n n' G,
  NoConflict n n' ->
  EnvTyped n G ->
  EnvTyped (env_union n n') G.
Proof.
  intros n n' G Hc Ht. generalize dependent n'. induction Ht; intros; simpl in *. { constructor. }
  - econstructor; [| eassumption]. cbn. destruct (n' x) as [n'x |] eqn:E; [| assumption].
    f_equal. symmetry. eapply Hc; eassumption.
  - constructor; [apply IHHt1 | apply IHHt2]; assumption.
  - constructor. { hauto l: on. } { hauto l: on. } destruct H;
    (eapply prop_on_weakening_alt in Hc; [| eassumption]); [left | right]; assumption.
Qed.
Hint Resolve env_typed_weakening_alt : core.

(* environment typing smart constructors *)
Theorem env_typed_singleton : forall x s p,
  PfxTyped p s ->
  EnvTyped (singleton_env x p) (CtxHasTy x s).
Proof.
  intros; econstructor; [| eauto]; cbn.
  unfold singleton_env.
  hauto lq: on use: eqb_refl.
Qed.

Theorem env_typed_comma: forall n n' g g',
  DisjointSets (dom n) (dom n') ->
  EnvTyped n g ->
  EnvTyped n' g' ->
  EnvTyped (env_union n n') (CtxComma g g').
Proof.
  constructor.
  + eapply env_typed_weakening_alt; [|eauto]. cbn in *. intros.
    specialize (H x) as [H _]. contradiction H; eexists; eassumption.
  + apply env_typed_weakening. assumption.
Qed.

Theorem env_typed_semic : forall n n' g g',
  DisjointSets (dom n) (dom n') ->
  EnvTyped n g ->
  EnvTyped n' g' ->
  EmptyOn (fv g') n' \/ MaximalOn (fv g) n ->
  EnvTyped (env_union n n') (CtxSemic g g').
Proof.
  constructor.
  + eapply env_typed_weakening_alt; [|eauto]. cbn in *. intros.
    specialize (H x) as [H _]. contradiction H; eexists; eassumption.
  + apply env_typed_weakening. assumption.
  + destruct H2; [left; apply prop_on_weakening | right; apply prop_on_weakening_alt]; try assumption.
    cbn in *. intros. specialize (H x) as [H _]. contradiction H; eexists; eassumption.
Qed.

(* specialized environment substitution theorems. These are the downstream facts we really need. *)
Theorem catlenvtyped : forall G x y z p1 p2 s t r n,
  x <> y ->
  n z = Some (PfxParPair p1 p2) ->
  PfxTyped p1 s ->
  PfxTyped p2 t ->
  EnvTyped n (fill G (CtxHasTy z r)) ->
  EnvTyped
    (env_union n (env_union (singleton_env x p1) (singleton_env y p2)))
    (fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t))).
Proof.
  best use: env_subctx_bind time: 10.

  intros G x y z p1 p2 s t r n Hxy Hnz Hp1 Hp2 He.
  remember (fill G (CtxHasTy z r)) as Gzr eqn:Ezr. apply reflect_fill in Ezr.
  remember (fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t))) as Gxsyt eqn:Exsyt. apply reflect_fill in Exsyt.
  generalize dependent x. generalize dependent y. generalize dependent z. generalize dependent p1.
  generalize dependent p2. generalize dependent s. generalize dependent t. generalize dependent r.
  generalize dependent n. generalize dependent Gzr. generalize dependent Gxsyt.
  induction G; cbn in *; intros; sinvert Ezr; sinvert Exsyt.
  - sinvert He. rewrite Hnz in H2. invert H2. constructor. best.


  generalize dependent x. generalize dependent y.
  generalize dependent p1. generalize dependent p2. generalize dependent s. generalize dependent t.
  (* induction He; cbn in *; intros. *)
  generalize dependent z. generalize dependent r. generalize dependent n. induction G; cbn in *; intros.
Qed.

Theorem catrenvtyped1 :  forall G x y z p1 s t r eta,
  x <> y ->
  eta z = Some (PfxCatFst p1) ->
  PfxTyped p1 s ->
  EnvTyped eta (fill G (CtxHasTy z r)) ->
  EnvTyped
  (env_union eta
     (env_union (singleton_env x p1) (singleton_env y (emp t))))
  (fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t))).
Proof.
Admitted.

Theorem catrenvtyped2 :  forall G x y z p1 p2 s t r eta,
  x <> y ->
  eta z = Some (PfxCatBoth p1 p2) ->
  PfxTyped p1 s ->
  PfxTyped p2 t ->
  MaximalPrefix p1 ->
  EnvTyped eta (fill G (CtxHasTy z r)) ->
  EnvTyped
  (env_union eta
     (env_union (singleton_env x p1) (singleton_env y p2)))
  (fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t))).
Proof.
Admitted.

(* i think this one needs stronger premises... *)
Theorem letenvtyped :  forall G D x p s eta,
  PfxTyped p s ->
  EnvTyped eta (fill G D) ->
  EnvTyped (env_subst x p eta) (fill G (CtxHasTy x s)).
Proof.
Admitted.

Theorem dropenvtyped :  forall G x s eta,
  EnvTyped eta (fill G (CtxHasTy x s)) ->
  EnvTyped (env_drop eta x) (fill G CtxEmpty).
Proof.
Admitted.

(* TODO: B.11 *)
