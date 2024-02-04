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
  Terms
  Types.

(* Definition B.8, part I *)
Definition env : Set := string -> option prefix.
Arguments env/.
Hint Unfold env : core.

Definition singleton_env (id : string) (p : prefix) : env := fun x =>
  if eqb id x then Some p else None.
Arguments singleton_env id p x/.
Hint Unfold singleton_env : core.

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

Definition env_subst (x : string) (p : prefix) (rho : env) : env :=
  env_union rho (singleton_env x p).
Arguments env_subst x p rho x/.
Hint Unfold env_subst : core.

Definition env_drop (n : env) (x : string) : env := fun y =>
  if eqb x y then None else n x.
Arguments env_drop n x y/.
Hint Unfold env_drop : core.

Definition EnvEq (n1 n2 : env) := forall x, n1 x = n2 x.
Arguments EnvEq n1 n2/.
Hint Unfold EnvEq : core.

(* Argument order matches notation: (EnvSub n1 n2) === (n1 <= n2) *)
Definition EnvSub (n1 n2 : env) := forall x n1x, n1 x = Some n1x -> n2 x = Some n1x.
Arguments EnvSub n1 n2/.
Hint Unfold EnvSub : core.

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
Arguments PropOnItem/ P n x.
Hint Unfold PropOnItem : core.

Definition PropOn (P : prefix -> Prop) (s : set string) (n : env) : Prop := forall x, s x -> PropOnItem P n x.
Arguments PropOn/ P s n.
Hint Unfold PropOn : core.

(* Definition B.7, part I *)
Definition EmptyOn := PropOn EmptyPrefix.
Arguments EmptyOn/ s n.
Hint Unfold EmptyOn : core.

(* Definition B.7, part II *)
Definition MaximalOn := PropOn MaximalPrefix.
Arguments MaximalOn/ s n.
Hint Unfold MaximalOn : core.

Definition B7 := PropOn.
Arguments B7/ P s n.

Theorem prop_on_subset : forall P s s' n,
  Subset s' s ->
  PropOn P s n ->
  PropOn P s' n.
Proof. sfirstorder. Qed.
Hint Resolve prop_on_subset : core.

Theorem prop_on_union: forall P s s' n,
  PropOn P (set_union s s') n <-> PropOn P s n /\ PropOn P s' n.
Proof. sfirstorder. Qed.
Hint Resolve prop_on_union : core.

(* Definition B.7, part III, heavily edited *)
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

(* Definition B.8, part II *)
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
Arguments EnvTyped n G.
Hint Constructors EnvTyped : core.

Definition B8 := EnvTyped.
Arguments B8/ n G.

(* Theorem B.9 *)
Theorem maps_to_hole : forall g d gd n,
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
Hint Resolve maps_to_hole : core.

Definition B9 := maps_to_hole.
Arguments B9/.

Theorem maps_to_hole_fn : forall n G D,
  EnvTyped n (fill G D) ->
  EnvTyped n D.
Proof.
  intros. remember (fill G D) as GD eqn:E. apply reflect_fill in E.
  eapply maps_to_hole; eassumption.
Qed.
Hint Resolve maps_to_hole_fn : core.

(* Theorem B.10, part II *)
Theorem maps_to_has_type : forall n G x Gxs s,
  Fill G (CtxHasTy x s) Gxs ->
  EnvTyped n Gxs ->
  exists p, (n x = Some p /\ PrefixTyped p s).
Proof.
  intros. assert (A := maps_to_hole _ _ _ _ H H0).
  sinvert A. repeat econstructor; eassumption.
Qed.
Hint Resolve maps_to_has_type : core.

Definition B10 := maps_to_has_type.
Arguments B10/.

Theorem maps_to_has_type_fn : forall n G x s,
  EnvTyped n (fill G (CtxHasTy x s)) ->
  exists p, (n x = Some p /\ PrefixTyped p s).
Proof. intros. assert (A := maps_to_hole_fn _ _ _ H). sinvert A. eexists. split; eassumption. Qed.
Hint Resolve maps_to_has_type_fn : core.

Definition NoConflict (n n' : env) := forall x p,
  n x = Some p ->
  forall p',
  n' x = Some p' ->
  p = p'.
Arguments NoConflict/ n n'.
Hint Unfold NoConflict : core.

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

(* A version of B.11 more specific than agreement: the exact same term *)
Theorem env_subctx_bind_equal : forall hole plug n n',
  NoConflict n n' ->
  EnvTyped n (fill hole plug) ->
  EnvTyped n' plug ->
  EnvTyped (env_union n n') (fill hole plug).
Proof.
  intros hole plug n n' Hc Hn Hn'.
  remember (fill hole plug) as ctx eqn:Ef. assert (Hf := Ef). apply reflect_fill in Hf.
  generalize dependent n. generalize dependent n'. generalize dependent Ef.
  induction Hf; hauto l: on.
Qed.
Hint Resolve env_subctx_bind_equal : core.

Lemma or_hyp : forall P Q R,
  ((P \/ Q) -> R) ->
  ((P -> R) /\ (Q -> R)).
Proof. sfirstorder. Qed.
Hint Resolve or_hyp : core.

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

(* Theorem B.11 *)
(* The only reason this is difficult is the extra disjunction in the environment-typing rule for semicolon contexts,
 * and that's why we need the `agree_union` lemma. *)
Theorem env_subctx_bind : forall hole plug plug' n n',
  NoConflict n n' ->
  EnvTyped n (fill hole plug) ->
  EnvTyped n' plug' ->
  Agree Inert n n' (fv plug) (fv plug') ->
  EnvTyped (env_union n n') (fill hole plug').
Proof.
  intros hole plug plug' n n' Hc Hn Hn' [Ham Hae].
  remember (fill hole plug) as ctx eqn:Hf. apply reflect_fill in Hf.
  remember (fill hole plug') as ctx' eqn:Hf'. apply reflect_fill in Hf'.
  generalize dependent plug'. generalize dependent n. generalize dependent n'. generalize dependent ctx'.
  induction Hf; cbn in *; intros; [sinvert Hf'; apply env_typed_weakening; assumption | | | |];
  sinvert Hf'; sinvert Hn; constructor; try (eapply IHHf; eassumption); clear IHHf;
  try (apply env_typed_weakening_alt; assumption); (* everything from here on is just the extra disjunction *)
  (destruct H5; [left | right]); try (apply prop_on_weakening_alt; eassumption); eapply agree_union; sfirstorder.
Qed.
Hint Resolve env_subctx_bind : core.

Definition B11 := env_subctx_bind.
Arguments B11/.

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

Theorem catlenvtyped : forall G x y z p1 p2 s t r n,
  x <> y ->
  NoConflict n (env_union (singleton_env x p1) (singleton_env y p2)) ->
  n z = Some (PfxParPair p1 p2) ->
  PrefixTyped p1 s ->
  PrefixTyped p2 t ->
  EnvTyped n (fill G (CtxHasTy z r)) ->
  EnvTyped
    (env_union n (env_union (singleton_env x p1) (singleton_env y p2)))
    (fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t))).
Proof.
  intros G x y z p1 p2 s t r n Hxy Hn Hnz Hp1 Hp2 He.
  eapply env_subctx_bind; [eassumption | eassumption | |].
  - constructor; (econstructor; [| eassumption]); cbn in *; rewrite eqb_refl; [| reflexivity].
    destruct (eqb_spec y x); [| reflexivity]. subst. contradiction Hxy. reflexivity.
  - split; intros; eapply empty_or_maximal_pfx_par_pair; try eassumption; [right | left]; reflexivity.
Qed.
Hint Resolve catlenvtyped : core.
