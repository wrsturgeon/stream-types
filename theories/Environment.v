From Coq Require Import
  List
  String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  FV
  Hole
  Inert
  Prefix
  Sets
  (* Terms *)
  Types.

Definition env : Set := string -> option prefix.
Hint Unfold env : core.

Definition empty_env : env := fun x => None.
Arguments empty_env/.
Hint Unfold empty_env : core.

Definition singleton_env (id : string) (p : prefix) : env := fun x =>
  if eqb id x then Some p else None.
Arguments singleton_env id p x/.
Hint Unfold singleton_env : core.

Definition env_union (n n' : env) : env := fun x =>
  match n' x with
  | None => n x
  | Some y => Some y
  end.
Arguments env_union n n' x/.
Hint Unfold env_union : core.

Definition env_subst (x : string) (p : prefix) (rho : env) : env :=
  env_union rho (singleton_env x p).
Arguments env_subst x p rho x/.
Hint Unfold env_subst : core.

Definition env_drop (n : env) (x : string) : env := fun y =>
  if eqb x y then None else n x.
Hint Unfold env_drop : core.

Definition dom (n : env) : set string :=
  fun x => exists p, n x = Some p.
Arguments dom n x/.
Hint Unfold dom : core.

Theorem dom_singleton : forall x p, SetEq (dom (singleton_env x p)) (singleton_set x).
Proof.
Admitted.

Theorem dom_union : forall env1 env2, SetEq (dom (env_union env1 env2)) (set_union (dom env1) (dom env2)).
Proof.
Admitted.

Theorem dom_subst : forall env x p, SetEq (dom (env_subst x p env)) (set_union (dom env) (singleton_set x)).
Proof.
Admitted.





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
  Subset s' s ->
  PropOn P s n ->
  PropOn P s' n.
Proof. sfirstorder. Qed.

Theorem prop_on_union: forall P s s' n,
  PropOn P (set_union s s') n <-> PropOn P s n /\ PropOn P s' n.
Proof. sfirstorder. Qed.

(* Agree Inert means "including empty on agreement";
 * Agree Jumpy means "not including empty on agreement." *)
Definition Agree (i : inertness) (n n' : env) (s s' : set string) : Prop :=
  (MaximalOn s n -> MaximalOn s' n') /\
  (i = Inert -> EmptyOn s n -> EmptyOn s' n').
Arguments Agree/ i n n' s s'.
Hint Unfold Agree : core.

Theorem agree_subset : forall i n s s',
  Subset s s' ->
  Agree i n n s' s.
Proof.
  intros.
  unfold Subset in H.
  sfirstorder.
Qed.
Hint Resolve agree_subset : core.


Inductive EnvTyped : env -> context -> Prop :=
  | EnvTyEmpty : forall n,
      EnvTyped n CtxEmpty
  | EnvTyHasTy : forall n p x s,
      n x = Some p ->
      PrefixTyped p s ->
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

Theorem envtyped_dom : forall eta g,
  EnvTyped eta g -> Subset (fv g) (dom eta).
Proof.
intros; induction H; hauto q: on use:dom_union.
Qed.


Fixpoint empty_env_for (g : context) : env :=
  match g with
  | CtxEmpty => empty_env
  | CtxHasTy x s => singleton_env x (emp s)
  | CtxComma g1 g2 | CtxSemic g1 g2 => env_union (empty_env_for g1) (empty_env_for g2)
  end.

(* TODO: will.
use the above smart constructors (dom_union, dom_singleton). *)
Theorem empty_env_for_dom : forall g, SetEq (dom (empty_env_for g)) (fv g).
Proof.
Admitted.


Theorem maps_to_hole_reflect : forall g d gd n,
  Fill g d gd ->
  EnvTyped n gd ->
  EnvTyped n d.
Proof.
  intros. generalize dependent g. generalize dependent d. induction H0; cbn in *; intros; subst.
 - sinvert H. constructor.
 - sinvert H1. econstructor; eassumption.
 - sinvert H; [constructor | eapply IHEnvTyped1 | eapply IHEnvTyped2]; eassumption.
 - sinvert H0; [constructor | eapply IHEnvTyped1 | eapply IHEnvTyped2]; eassumption.
Qed.
Hint Resolve maps_to_hole_reflect : core.

(* Theorem B.9 *)
Theorem maps_to_hole : forall n G D,
  EnvTyped n (fill G D) ->
  EnvTyped n D.
Proof.
  intros. remember (fill G D) as GD eqn:E. apply reflect_fill in E.
  eapply maps_to_hole_reflect; eassumption.
Qed.
Hint Resolve maps_to_hole : core.

(* Theorem B.10, part II *)
Theorem maps_to_has_type : forall n G x s,
  EnvTyped n (fill G (CtxHasTy x s)) ->
  exists p, (n x = Some p /\ PrefixTyped p s).
Proof. intros. assert (A := maps_to_hole _ _ _ H). sinvert A. eexists. split; eassumption. Qed.
Hint Resolve maps_to_has_type : core.

Theorem maps_to_has_type_reflect : forall n G x Gx s,
  Fill G (CtxHasTy x s) Gx ->
  EnvTyped n Gx ->
  exists p, (n x = Some p /\ PrefixTyped p s).
Proof. intros. assert (A := maps_to_hole_reflect _ _ _ _ H H0). sinvert A. repeat econstructor; eassumption. Qed.
Hint Resolve maps_to_has_type : core.

Definition NoConflict (n n' : env) := forall x p p',
  n x = Some p ->
  n' x = Some p' ->
  p = p'.
Arguments NoConflict/ n n'.
Hint Unfold NoConflict : core.

Definition NoConflictOn (n n' : env) s := forall x p p',
  s x ->
  n x = Some p ->
  n' x = Some p' ->
  p = p'.
Arguments NoConflictOn/ n n' s.
Hint Unfold NoConflictOn : core.

Theorem NoConflictOn_union : forall eta eta' s s',
  NoConflictOn eta eta' (set_union s s') <-> (NoConflictOn eta eta' s /\ NoConflictOn eta eta' s').
Proof.
sfirstorder.
Qed.

Lemma prop_on_fill : forall P n d d' g lhs lhs',
  Fill g d lhs ->
  Fill g d' lhs' ->
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

Lemma prop_on_fill_iff : forall P n h d g,
  Fill h d g -> (
    (PropOn P (fv h) n /\ PropOn P (fv d) n) <->
    PropOn P (fv g) n).
Proof. intros. apply fv_fill in H. split; sfirstorder. Qed.
Hint Resolve prop_on_fill_iff : core.

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

Lemma env_typed_weakening_alt' : forall n n' g,
  NoConflictOn n n' (fv g) ->
  EnvTyped n g ->
  EnvTyped (env_union n n') g.
Proof.
  intros. generalize dependent n'. induction H0; cbn in *; intros.
  - constructor.
  - econstructor; [| eassumption]. cbn. destruct (n' x) eqn:E; [| assumption].
    f_equal. symmetry. eapply H1; [reflexivity | |]; assumption.
  - constructor; [apply IHEnvTyped1 | apply IHEnvTyped2];
    intros; (eapply H; [| eassumption | assumption]);
    [left | right]; assumption.
  - constructor; [apply IHEnvTyped1 | apply IHEnvTyped2 | shelve];
    intros; (eapply H0; [| eassumption | assumption]);
    [left | right]; assumption. Unshelve.
    destruct H; [left | right]; cbn; intros x Hx; specialize (H x Hx) as [p [Ep Hp]];
    exists p; (split; [| apply Hp]); (destruct (n' x) eqn:E; [| assumption]);
    f_equal; symmetry; (eapply H0; [| eassumption | eassumption]); [right | left]; assumption.
Qed.
Hint Resolve env_typed_weakening_alt' : core.

(* environment typing smart constructors *)
Theorem env_typed_singleton : forall x s p,
  PrefixTyped p s ->
  EnvTyped (singleton_env x p) (CtxHasTy x s).
Proof.
  intros; econstructor; [| eauto]; cbn.
  unfold singleton_env.
  hauto lq: on use: eqb_refl.
Qed.
Hint Resolve env_typed_singleton : core.

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
Hint Resolve env_typed_comma : core.

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
Hint Resolve env_typed_semic : core.


(* todo: emptyenv_for *)
(* need to use the empty_env_dom theorem, otherwise easy. *)
Theorem empty_env_for_typed : forall g, EnvTyped (empty_env_for g) g.
Proof.
intros.
induction g.
Admitted.

Theorem empty_env_for_empty : forall g, EmptyOn (fv g) (empty_env_for g).
Proof.
intros.
induction g.
Admitted.



Lemma agree_union : forall P n n' D D' lhs lhs' lhs'',
  NoConflict n n' ->
  (PropOn P (fv D) n -> PropOn P (fv D') n') ->
  Fill lhs D  lhs'  ->
  Fill lhs D' lhs'' ->
  PropOn P (fv lhs') n ->
  PropOn P (fv lhs'') (env_union n n').
Proof.
  intros P n n' D D' lhs lhs' lhs'' Hn Hp Hf Hf' H. generalize dependent P. generalize dependent n.
  generalize dependent n'. generalize dependent D'. generalize dependent lhs''.
  induction Hf; intros; sinvert Hf'; [hauto l: on | | | |];
  intros x [Hfv | Hfv]; try (eapply IHHf; clear IHHf; [| assumption | eassumption | | eassumption];
    [assumption |]; intros x' H'; apply H; try (left; assumption); right; assumption); clear IHHf;
  try assert (A := H _ (or_intror Hfv)); try assert (A := H _ (or_introl Hfv)); destruct A as [p [Hnx HP]];
  exists p; cbn; (destruct (n' x) eqn:E; split; [f_equal; symmetry; eapply Hn | | |]); eassumption.
Qed.
Hint Resolve agree_union : core.


Theorem env_subctx_bind' : forall h d d' hd hd' eta eta',
  Fill h d hd ->
  Fill h d' hd' ->
  NoConflictOn eta eta' (fv h) ->
  EnvTyped eta hd ->
  EnvTyped eta' d' ->
  Agree Inert eta eta' (fv d) (fv d') ->
  EnvTyped (env_union eta eta') hd'.
Proof.
  intros.
  generalize dependent d'.
  generalize dependent hd'.
  generalize dependent eta'.
  generalize dependent eta.
  induction H; intros.
  - sauto l: on.
  - sinvert H0; sinvert H2; econstructor; [hauto l: on | hauto l:on use: env_typed_weakening_alt'].
  - sinvert H0; sinvert H2; econstructor; hauto l: on.
  - sinvert H0; sinvert H2; econstructor; [qauto l:on | hauto l:on |].
    destruct H10; [left | right].
    + unfold NoConflictOn in H1. unfold EmptyOn in *. unfold PropOn in *.
      intros. edestruct H0 as [p]; eauto. 
      exists p. hauto q: on.
    + unfold NoConflictOn in H0. unfold MaximalOn in *. unfold PropOn in *. unfold PropOnItem in *.
      intros.
      assert (fv h x \/ fv d' x) by hauto q: on use:fv_fill.
      destruct H5.
      * edestruct H0 as [p]. qauto l: on use:fv_fill. exists p; hauto q: on.
      * assert (MaximalOn (fv d') eta') by qauto l:on use:fv_fill; edestruct H7 as [p]; eauto; exists p; hauto q: on.
  - sinvert H0; sinvert H2; econstructor; [hauto l:on | qauto l:on |].
    destruct H10; [left | right].
    + unfold NoConflictOn in H1. unfold EmptyOn in *. unfold PropOn in *.
      intros. 
      assert (fv h x \/ fv d' x) by hauto q: on use:fv_fill.
      destruct H5.
      * edestruct H0 as [p]. qauto l: on use:fv_fill. exists p; hauto q: on.
      * assert (EmptyOn (fv d') eta') by qauto l:on use:fv_fill; edestruct H7 as [p]; eauto; exists p; hauto q: on.
    + unfold NoConflictOn in H1. unfold MaximalOn in *. unfold PropOn in *.
      intros. edestruct H0 as [p]; eauto. 
      exists p. hauto q: on.
Qed.

Lemma empty_or_maximal_pfx_par_pair : forall P x y z n p1 p2,
  (P = EmptyPrefix \/ P = MaximalPrefix) ->
  x <> y ->
  n z = Some (PfxParPair p1 p2) -> (
    PropOn P (singleton_set z) n <->
    PropOn P (set_union (singleton_set x) (singleton_set y)) (env_union (singleton_env x p1) (singleton_env y p2))).
Proof.
  simpl fv. intros P x y z n p1 p2 HP Hxy Hnz. split; cbn in *; intros.
  - specialize (H _ eq_refl) as [p [Hnzp Hmp]]. rewrite Hnz in Hnzp. sinvert Hnzp. destruct HP; (subst; sinvert Hmp;
    destruct H0; subst; [apply eqb_neq in Hxy; rewrite eqb_sym in Hxy; rewrite Hxy |]; rewrite eqb_refl; sfirstorder).
  - subst. eexists. split. { eassumption. } destruct HP; (subst;
    constructor; [specialize (H _ (or_introl eq_refl)) | specialize (H _ (or_intror eq_refl))];
    [apply eqb_neq in Hxy; rewrite eqb_sym in Hxy; rewrite Hxy in H |];
    rewrite eqb_refl in H; destruct H as [p [Ep Hp]]; sinvert Ep; assumption).
Qed.
Hint Resolve empty_or_maximal_pfx_par_pair : core.

Theorem parlenvtyped : forall G Gz Gxy x y z p1 p2 s t r n,
  x <> y ->
  (~ fv G x) ->
  (~ fv G y) ->
  n z = Some (PfxParPair p1 p2) ->
  PrefixTyped p1 s ->
  PrefixTyped p2 t ->
  Fill G (CtxHasTy z r) Gz ->
  Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxy ->
  EnvTyped n Gz ->
  EnvTyped
    (env_union n (env_union (singleton_env x p1) (singleton_env y p2)))
    Gxy.
Proof.
  cbn. intros. eapply env_subctx_bind'; [| eassumption | | eassumption | |]. { eassumption. }
  - cbn. intros test p p' Htest Etest. destruct (eqb_spec y test). { congruence. }
    destruct (eqb_spec x test). { congruence. } intro C; discriminate C.
  - apply eqb_neq in H. rewrite eqb_sym in H. constructor;
    (econstructor; [cbn; rewrite eqb_refl; try rewrite H; reflexivity |]); assumption.
  - split; [intros HH | intros _ HH]; specialize (HH _ eq_refl) as [p [Ep Hp]];
    rewrite H2 in Ep; sinvert Ep; sinvert Hp; intros test Htest; cbn;
    (destruct (eqb_spec y test); [eexists; split; [reflexivity | assumption] |]);
    (destruct (eqb_spec x test); [eexists; split; [reflexivity | assumption] |]);
    cbn in Htest; destruct Htest; tauto.
Qed.

Theorem catrenvtyped1 :  forall G Gz Gxy x y z p1 s t r eta,
  x <> y ->
  (~ fv G x) ->
  (~ fv G y) ->
  eta z = Some (PfxCatFst p1) ->
  PrefixTyped p1 s ->
  Fill G (CtxHasTy z r) Gz ->
  Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxy ->
  EnvTyped eta Gz ->
  EnvTyped
  (env_union eta
     (env_union (singleton_env x p1) (singleton_env y (emp t))))
  Gxy.
Proof.
  cbn. intros. eapply env_subctx_bind'; [| eassumption | | eassumption | |]. { eassumption. }
  - cbn. intros test p p' Htest Etest. destruct (eqb_spec y test). { congruence. }
    destruct (eqb_spec x test). { congruence. } intro C; discriminate C.
  - apply eqb_neq in H. rewrite eqb_sym in H. constructor; [| | shelve];
    econstructor; [| eassumption | | apply emp_well_typed]; cbn; [rewrite H |]; rewrite eqb_refl; reflexivity.
    Unshelve. left. cbn. intros v Hv. subst. rewrite eqb_refl. eexists. split; [reflexivity |]. apply emp_empty.
  - split; [intros HH | intros _ HH]; specialize (HH _ eq_refl) as [p [Ep Hp]];
    rewrite H2 in Ep; sinvert Ep; sinvert Hp. intros test Htest. cbn.
    destruct (eqb_spec y test); [eexists; split; [reflexivity | apply emp_empty] |].
    destruct (eqb_spec x test); [eexists; split; [reflexivity | assumption] |].
    cbn in Htest; destruct Htest; tauto.
Qed.

Theorem catrenvtyped2 :  forall G Gz Gxy x y z p1 p2 s t r eta,
  x <> y ->
  (~ fv G x) ->
  (~ fv G y) ->
  eta z = Some (PfxCatBoth p1 p2) ->
  PrefixTyped p1 s ->
  PrefixTyped p2 t ->
  MaximalPrefix p1 ->
  Fill G (CtxHasTy z r) Gz ->
  Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxy ->
  EnvTyped eta Gz ->
  EnvTyped
  (env_union eta
     (env_union (singleton_env x p1) (singleton_env y p2)))
  Gxy.
Proof.
  cbn. intros. eapply env_subctx_bind'; [| eassumption | | eassumption | |]. { eassumption. }
  - cbn. intros test p p' Htest Etest. destruct (eqb_spec y test). { congruence. }
    destruct (eqb_spec x test). { congruence. } intro C; discriminate C.
  - apply eqb_neq in H. rewrite eqb_sym in H. constructor; [| | shelve];
    (econstructor; [| eassumption]); cbn; [rewrite H |]; rewrite eqb_refl; reflexivity.
    Unshelve. right. cbn. intros v Hv. subst. rewrite H. rewrite eqb_refl.
    eexists. split. { reflexivity. } assumption.
  - split; [intros HH | intros _ HH]; specialize (HH _ eq_refl) as [p [Ep Hp]];
    rewrite H2 in Ep; sinvert Ep; sinvert Hp. intros test Htest. cbn.
    destruct (eqb_spec y test). { subst. eexists. split. { reflexivity. } assumption. }
    destruct (eqb_spec x test). { subst. eexists. split. { reflexivity. } assumption. }
    cbn in Htest; destruct Htest; tauto.
Qed.

(* TODO: will *)
Theorem letenvtyped :  forall G D GD Gx x p s eta,
  Agree Inert eta (singleton_env x p) (fv D) (singleton_set x) ->
  PrefixTyped p s ->
  Fill G D GD ->
  Fill G (CtxHasTy x s) Gx ->
  EnvTyped eta GD ->
  EnvTyped (env_subst x p eta) Gx.
Proof.
Admitted.

(* TODO: will *)
Theorem dropenvtyped :  forall G Gx GE x s eta,
  Fill G (CtxHasTy x s) Gx ->
  Fill G CtxEmpty GE ->
  EnvTyped eta Gx ->
  EnvTyped (env_drop eta x) GE.
Proof.
Admitted.

Theorem sumcaseenvtyped1 : forall G Gz Gx x z p s r n,
  (~ fv G x) ->
  n z = Some (PfxSumInl p) ->
  PrefixTyped p s ->
  Fill G (CtxHasTy z r) Gz ->
  Fill G (CtxHasTy x s) Gx ->
  EnvTyped n Gz ->
  EnvTyped
    (env_union n (singleton_env x p)) Gx.
Proof.
Admitted.

Theorem sumcaseenvtyped2 : forall G Gz Gx x z p s r n,
  (~ fv G x) ->
  n z = Some (PfxSumInr p) ->
  PrefixTyped p s ->
  Fill G (CtxHasTy z r) Gz ->
  Fill G (CtxHasTy x s) Gx ->
  EnvTyped n Gz ->
  EnvTyped
    (env_union n (singleton_env x p)) Gx.
Proof.
Admitted.