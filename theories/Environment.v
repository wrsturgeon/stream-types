From Coq Require Import
  List.
From Hammer Require Import
  Tactics.
From LambdaST Require Import
  Context
  FV
  Hole
  Ident
  Prefix
  Terms
  Types.

Definition env : Set := ident -> option prefix.
Hint Unfold env : core.

Definition dom (n : env) : set ident :=
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

Definition env_drop (n : env) (x : ident) : env := fun y =>
  if eq_id x y then None else n x.

Definition singleton_env (id : ident) (p : prefix) : env := fun x =>
  if eq_id id x then Some p else None.
Arguments singleton_env id p x/.
Hint Unfold singleton_env : core.

Definition subst (x : ident) (p : prefix) (rho : env) : env :=
  env_union rho (singleton_env x p).
Arguments subst x p rho x/.
Hint Unfold subst : core.

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
Definition PropOnItem (P : prefix -> Prop) (n : env) (x : ident) : Prop :=
  exists p, n x = Some p /\ P p.
Arguments PropOnItem P n x/.
Hint Unfold PropOnItem : core.

Definition PropOn (P : prefix -> Prop) (s : set ident) (n : env) : Prop := forall x, s x -> PropOnItem P n x.
Arguments PropOn/ P s n.
Hint Unfold PropOn : core.

Definition EmptyOn := PropOn EmptyPrefix.
Arguments EmptyOn/ s n.
Hint Unfold EmptyOn : core.

Definition MaximalOn := PropOn MaximalPrefix.
Arguments MaximalOn/ s n.
Hint Unfold MaximalOn : core.

Theorem prop_on_contains : forall P s s' n,
  Contains s s' ->
  PropOn P s' n ->
  PropOn P s n.
Proof. sfirstorder. Qed.

Theorem prop_on_union: forall P s s' n,
  PropOn P (set_union s s') n <-> PropOn P s n /\ PropOn P s' n.
Proof.
sfirstorder.
Qed.


Definition Agree n n' (D : context) (D' : context) : Prop :=
  (MaximalOn (fv D) n <-> MaximalOn (fv D') n') /\ (EmptyOn (fv D) n <-> EmptyOn (fv D') n').
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

Lemma prop_on_item_weakening : forall P n n' vs,
  PropOnItem P n' vs ->
  PropOnItem P (env_union n n') vs.
Proof. intros P n n' vs [p [Hn' Hp]]. exists p. split; [| assumption]. cbn. rewrite Hn'. reflexivity. Qed.
Hint Resolve prop_on_item_weakening : core.

Lemma env_typed_weakening : forall n n' G,
  EnvTyped n' G ->
  EnvTyped (env_union n n') G.
Proof.
  intros n n' G H. generalize dependent n.
  induction H; intros; econstructor; hauto lq: on.
Qed.
Hint Resolve env_typed_weakening : core.

Definition NoConflictOn (s : set ident) (n n' : env) := forall x p,
  s x -> n x = Some p -> (n' x = None \/ n' x = Some p).
Arguments NoConflictOn/ s n n'.
Hint Unfold NoConflictOn : core.

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
Hint Resolve env_typed_weakening_alt : core.

Lemma prop_on_union_fill : forall P n n' d d' h hd hd',
  NoConflictOn (fv h) n n' ->
  (PropOn P (fv d) n -> PropOn P (fv d') n') ->
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
  intros P n n' d d' h hd hd' Hc Ha Hf Hf' Hp. generalize dependent P. generalize dependent n.
  generalize dependent n'. generalize dependent d'. generalize dependent hd'.
  induction Hf; intros; sinvert Hf'; intros.
  - sauto lq: on.
  - apply prop_on_union. split.
    + hauto l: on.
    + admit.
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
    + eapply IHE. eauto. eauto. eapply no_conflict_contains; [|eauto]; sfirstorder.
      sauto lq: on. sfirstorder. sfirstorder.
    + sauto q: on use:env_typed_weakening_alt.
  - sinvert E'. constructor. 
    + sauto q: on use:env_typed_weakening_alt.
    + eapply IHE. eauto. eauto. eapply no_conflict_contains; [|eauto]; sfirstorder.
      sauto lq: on. sfirstorder. sfirstorder.
  - sinvert E'. constructor.
    + eapply IHE. eauto. eauto. eapply no_conflict_contains; [|eauto]; sfirstorder.
      sauto lq: on. sfirstorder. sfirstorder.
    + sauto q: on use:env_typed_weakening_alt.
    + sinvert Ht. destruct H5; [left | right].
  - admit.
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

(* specialized environment substitution theorems. These are the downstream facts we really need. *)
Theorem catlenvtyped :  forall G x y z p1 p2 s t r eta,
  x <> y ->
  eta z = Some (PfxParPair p1 p2) ->
  PfxTyped p1 s ->
  PfxTyped p2 t ->
  EnvTyped eta (fill G (CtxHasTy z r)) ->
  EnvTyped
  (env_union eta
     (env_union (singleton_env x p1) (singleton_env y p2)))
  (fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t))).
Proof.
  intros.
  assert ((x =i y) = false) by sfirstorder.
  assert ((y =i x) = false) by sfirstorder.
  assert ((x =i x) = true) by sfirstorder.
  assert ((y =i y) = true) by sfirstorder.
  eapply fill_replace; [|eauto| |].
  - admit.
  - eapply env_typed_comma; [| eapply env_typed_singleton; eauto | eapply env_typed_singleton; eauto]. admit.
  - unfold Agree. split; split; intros HPo; cbn in *; edestruct (HPo z); eauto; admit.
Admitted.

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
  Agree eta (singleton_env x p) D (CtxHasTy x s) ->
  PfxTyped p s ->
  EnvTyped eta (fill G D) ->
  EnvTyped (subst x p eta) (fill G (CtxHasTy x s)).
Proof.
Admitted.

Theorem dropenvtyped :  forall G x s eta,
  EnvTyped eta (fill G (CtxHasTy x s)) ->
  EnvTyped (env_drop eta x) (fill G CtxEmpty).
Proof.
Admitted.