Require Import Coq.Program.Equality.
From Coq Require Import String.
From LambdaST Require Import
  Context
  Environment
  Nullable
  Sets
  Hole
  Prefix
  FV
  Types.
From Hammer Require Import Tactics.

(* Intuition: things you can append to a thing of type T should have type (its derivative)
 * With jargon, concatenation is meaningful only between a prefix of type T and something of type (its derivative) *)
Inductive Derivative : prefix -> type -> type -> Prop :=
    (* You can append nothing to nothing *)
  | DrvEpsEmp :
      Derivative PfxEpsEmp eps eps
    (* You can receive a one where you expect a one and end up having a one *)
  | DrvOneEmp :
      Derivative PfxOneEmp 1 1
    (* You can append nothing to a received one *)
  | DrvOneFull :
      Derivative PfxOneFull 1 eps
    (* If you've received some stuff from parallel streams, you can receive more, regardless of which side *)
  | DrvParPair : forall p1 p2 s s' t t',
      Derivative p1 s s' ->
      Derivative p2 t t' ->
      Derivative (PfxParPair p1 p2) (TyPar s t) (TyPar s' t')
    (* You can receive an (s' . t) after an (s . t) if the `s` hasn't finished yet *)
  | DrvCatFst : forall p s s' t,
      Derivative p s s' ->
      Derivative (PfxCatFst p) (TyDot s t) (TyDot s' t)
    (* You can receive an (s . t') after an (s . t) if the `s` has already finished *)
  | DrvCatBoth : forall p1 p2 s t t',
      Derivative p2 t t' ->
      (* MaximalPrefix p1 -> *)
      Derivative (PfxCatBoth p1 p2) (TyDot s t) t'
    (* If you haven't gotten anything yet, you can receive either side of a sum *)
  | DrvSumEmp : forall s t,
      Derivative PfxSumEmp (TySum s t) (TySum s t)
    (* If you've already received from the left side of a sum, continue receiving that side *)
  | DrvSumInl : forall p s s' t,
      Derivative p s s' ->
      Derivative (PfxSumInl p) (TySum s t) s'
    (* TODO: this was almost certainly a typo in the appendix *)
    (* If you've already received from the right side of a sum, continue receiving that side *)
  | DrvSumInr : forall p s t t',
      Derivative p t t' ->
      Derivative (PfxSumInr p) (TySum s t) t'
    (* If you're expecting a star and haven't gotten anything yet, receive a star *)
  | DrvStarEmp : forall s,
      Derivative PfxStarEmp (TyStar s) (TyStar s)
    (* Nothing can follow the end of a star *)
  | DrvStarDone : forall s,
      Derivative PfxStarDone (TyStar s) eps
    (* If you just received the first element of a star, ... TODO: this is probably the most obscure one *)
  | DrvStarFirst : forall p s s',
      Derivative p s s' ->
      Derivative (PfxStarFirst p) (TyStar s) (TyDot s' (TyStar s))
    (* If you've already received some of a star, receive one at a time (TODO: verify) *)
  | DrvStarRest : forall p p' s s',
      Derivative p' (TyStar s) s' ->
      (* MaximalPrefix p -> *)
      Derivative (PfxStarRest p p') (TyStar s) s'
  .
Hint Constructors Derivative : core.

(* Recurse on all variables in context, use the above relation on each, then put them back exactly where they were *)
Inductive ContextDerivative : env -> context -> context -> Prop :=
  | CtxDrvEmpty : forall n,
      ContextDerivative n CtxEmpty CtxEmpty
    (* On each variable, "call" the above inductive definition *)
  | CtxDrvHasTy : forall n x p s s',
      n x = Some p ->
      Derivative p s s' ->
      ContextDerivative n (CtxHasTy x s) (CtxHasTy x s')
  | CtxDrvComma : forall n G G' D D',
      ContextDerivative n G G' ->
      ContextDerivative n D D' ->
      ContextDerivative n (CtxComma G D) (CtxComma G' D')
  | CtxDrvSemic : forall n G G' D D',
      ContextDerivative n G G' ->
      ContextDerivative n D D' ->
      ContextDerivative n (CtxSemic G D) (CtxSemic G' D')
  .
Hint Constructors ContextDerivative : core.

Inductive HoleDerivative : env -> hole -> hole -> Prop :=
  | HoleDrvHere : forall eta,
      HoleDerivative eta HoleHere HoleHere
  | HoleDrvCommaL : forall eta h h' g g',
      HoleDerivative eta h h' ->
      ContextDerivative eta g g' ->
      HoleDerivative eta (HoleCommaL h g) (HoleCommaL h' g')
  | HoleDrvCommaR : forall eta h h' g g',
      HoleDerivative eta h h' ->
      ContextDerivative eta g g' ->
      HoleDerivative eta (HoleCommaR g h) (HoleCommaR g' h')
  | HoleDrvSemicL : forall eta h h' g g',
      HoleDerivative eta h h' ->
      ContextDerivative eta g g' ->
      HoleDerivative eta (HoleSemicL h g) (HoleSemicL h' g')
  | HoleDrvSemicR : forall eta h h' g g',
      HoleDerivative eta h h' ->
      ContextDerivative eta g g' ->
      HoleDerivative eta (HoleSemicR g h) (HoleSemicR g' h')
  .
Hint Constructors ContextDerivative : core.

(* Theorem B.15, part I *)
Theorem derivative_det : forall p s s'1 s'2,
  Derivative p s s'1 ->
  Derivative p s s'2 ->
  s'1 = s'2.
Proof.
  intros p s s'1 s'2 H1 H2. generalize dependent s'2. induction H1; intros;
  sinvert H2; try reflexivity; auto.
  - apply IHDerivative1 in H5. apply IHDerivative2 in H6. subst. reflexivity.
  - apply IHDerivative in H5. subst. reflexivity.
  - apply IHDerivative in H3. subst. reflexivity.
Qed.
Hint Resolve derivative_det : core.

(* Theorem B.15, part II *)
Theorem derivative_fun : forall p s,
  PrefixTyped p s ->
  exists s', Derivative p s s'.
Proof.
  intros p s H. induction H; try solve [eexists; constructor];
  try destruct IHPrefixTyped as [s' Hd];
  try destruct IHPrefixTyped1 as [s' Hd1];
  try destruct IHPrefixTyped2 as [t' Hd2].
  - exists (TyPar s' t'). constructor; assumption.
  - exists (TyDot s' t). constructor. assumption.
  - exists t'. constructor; assumption.
  - exists s'. constructor. assumption.
  - exists s'. constructor. assumption.
  - exists (TyDot s' (TyStar s)). constructor. assumption.
  - exists t'. constructor; assumption.
Qed.
Hint Resolve derivative_fun : core.

(* Theorem B.16 *)
Theorem derivative_emp : forall s,
  Derivative (emp s) s s.
Proof. induction s; cbn; constructor; assumption. Qed.
Hint Resolve derivative_emp : core.

Theorem derivative_emp' : forall s s' p,
  EmptyPrefix p ->
  Derivative p s s' ->
  s' = s .
Proof.
  intros.
  induction H0; sauto lq: on rew: off.
Qed.

(* Theorem B.17, part I *)
Theorem context_derivative_det : forall n G G'1 G'2,
  ContextDerivative n G G'1 ->
  ContextDerivative n G G'2 ->
  G'1 = G'2.
Proof.
  intros n G G'1 G'2 H1 H2. generalize dependent G'2. induction H1; intros;
  sinvert H2; try (apply IHContextDerivative1 in H3; apply IHContextDerivative2 in H5; subst); try reflexivity.
  remember (maps_to_unique _ _ _ _ H H5) as U eqn:E. clear E. subst.
  remember (derivative_det _ _ _ _ H0 H7) as U eqn:E. clear E. subst.
  reflexivity.
Qed.
Hint Resolve context_derivative_det : core.

(* Theorem B.17, part II *)
Theorem context_derivative_fun : forall n G,
  EnvTyped n G ->
  exists G', ContextDerivative n G G'.
Proof.
  intros n G H. induction H;
  try (destruct IHEnvTyped1 as [G' HG]; destruct IHEnvTyped2 as [D' HD]);
  try (remember (derivative_fun p s H0) as D eqn:E; clear E; destruct D as [s' D]);
  eexists; econstructor; try apply H; try apply HG; try apply HD; apply D.
Qed.
Hint Resolve context_derivative_fun : core.

Theorem fv_context_derivative : forall eta g g',
  ContextDerivative eta g g' ->
  SetEq (fv g) (fv g').
Proof.
  intros. induction H; try rename x into x'; intro x; cbn in *; [split; intros [] | split; intro A; apply A | |];
  split; intros [Hf | Hf]; try apply IHContextDerivative1 in Hf; try apply IHContextDerivative2 in Hf;
  try (left; assumption); right; assumption.
Qed.
Hint Resolve fv_context_derivative : core.

Theorem fv_hole_derivative : forall eta h h',
  HoleDerivative eta h h' ->
  SetEq (fv h) (fv h').
Proof.
  intros. induction H; intro x; cbn in *; [split; intros [] | | | |];
  apply fv_context_derivative in H0; split; intros [Hf | Hf];
  try apply H0 in Hf; try apply IHHoleDerivative in Hf; try (left; assumption); right; assumption.
Qed.
Hint Resolve fv_hole_derivative : core.

Theorem context_derivative_wf : forall eta g g',
  WFContext g ->
  ContextDerivative eta g g' ->
  WFContext g'.
Proof.
  intros eta g g' Hw Hd. generalize dependent Hw. induction Hd; cbn in *; intros; constructor;
  sinvert Hw; try apply IHHd1; try apply IHHd2; try assumption; split; intros Hf C;
  apply fv_context_derivative in Hd1; apply fv_context_derivative in Hd2; cbn in *; sfirstorder.
Qed.
Hint Resolve context_derivative_wf : core.

Theorem context_derivative_wf' : forall eta g g',
  WFContext g' ->
  ContextDerivative eta g g' ->
  WFContext g.
Proof.
  intros eta g g' Hw Hd. generalize dependent Hw. induction Hd; cbn in *; intros; constructor;
  sinvert Hw; try apply IHHd1; try apply IHHd2; try assumption; split; intros Hf C;
  apply fv_context_derivative in Hd1; apply fv_context_derivative in Hd2; cbn in *; sfirstorder.
  (* happened to be the exact same proof (automation) as above *)
Qed.
Hint Resolve context_derivative_wf' : core.

Theorem hole_derivative_wf : forall eta h h',
  WFHole h ->
  HoleDerivative eta h h' ->
  WFHole h'.
Proof.
  intros eta g g' Hw Hd. generalize dependent Hw. induction Hd; cbn in *; intros; constructor;
  sinvert Hw; try apply IHHd; try eapply context_derivative_wf; try eassumption; split; intros Hf C;
  apply fv_hole_derivative in Hd; apply fv_context_derivative in H; cbn in *; sfirstorder.
Qed.
Hint Resolve hole_derivative_wf : core.


Theorem hole_derivative_fun : forall eta h d hd,
  Fill h d hd ->
  EnvTyped eta hd ->
  exists h', HoleDerivative eta h h'.
Proof.
  intros eta h d hd Hf Ht. generalize dependent eta. generalize dependent d. generalize dependent hd.
  induction h; cbn in *; intros; sinvert Hf.
  - eexists. constructor.
  - sinvert Ht. specialize (IHh _ _ H3 _ H2) as [h' Hh'].
    destruct (context_derivative_fun _ _ H4) as [g' Hg'].
    eexists. constructor; eassumption.
  - sinvert Ht. specialize (IHh _ _ H3 _ H4) as [h' Hh'].
    destruct (context_derivative_fun _ _ H2) as [g' Hg'].
    eexists. constructor; eassumption.
  - sinvert Ht. specialize (IHh _ _ H3 _ H1) as [h' Hh'].
    destruct (context_derivative_fun _ _ H4) as [g' Hg'].
    eexists. constructor; eassumption.
  - sinvert Ht. specialize (IHh _ _ H3 _ H4) as [h' Hh'].
    destruct (context_derivative_fun _ _ H1) as [g' Hg'].
    eexists. constructor; eassumption.
Qed.
Hint Resolve hole_derivative_fun : core.

Theorem hole_derivative_det : forall eta h h' h'',
  HoleDerivative eta h h' ->
  HoleDerivative eta h h'' ->
  h' = h''.
Proof.
  intros eta h h' h'' H. generalize dependent h''. induction H; cbn in *; intros;
  [sinvert H; reflexivity | | | |]; sinvert H1; rewrite (context_derivative_det _ _ _ _ H0 H7);
  subst; f_equal; apply IHHoleDerivative; assumption.
Qed.
Hint Resolve hole_derivative_det : core.

Theorem context_derivative_overwrite : forall eta eta' g g',
  ContextDerivative eta' g g' ->
  ContextDerivative (env_union eta eta') g g'.
Proof.
  intros. generalize dependent eta. induction H; cbn in *; intros.
  - constructor.
  - econstructor; cbn. { rewrite H. reflexivity. } assumption.
  - constructor; [apply IHContextDerivative1 | apply IHContextDerivative2].
  - constructor; [apply IHContextDerivative1 | apply IHContextDerivative2].
Qed.
Hint Resolve context_derivative_overwrite : core.

Theorem context_derivative_noconflict : forall eta eta' g g',
  NoConflictOn eta eta' (fv g) ->
  ContextDerivative eta g g' ->
  ContextDerivative (env_union eta eta') g g'.
Proof.
  intros. generalize dependent eta'. induction H0; cbn in *; intros.
  - constructor.
  - econstructor; cbn; [| eassumption]. destruct (eta' x) eqn:E; [| eassumption].
    f_equal. symmetry. eapply H1; [reflexivity | |]; assumption.
  - constructor; [apply IHContextDerivative1 | apply IHContextDerivative2];
    intros; eapply H; try eassumption; [left | right]; assumption.
  - constructor; [apply IHContextDerivative1 | apply IHContextDerivative2];
    intros; eapply H; try eassumption; [left | right]; assumption.
Qed.
Hint Resolve context_derivative_noconflict : core.

Theorem context_derivative_sng: forall x p s s',
  Derivative p s s' ->
  ContextDerivative (singleton_env x p) (CtxHasTy x s) (CtxHasTy x s').
Proof. intros. econstructor; cbn. { rewrite eqb_refl. reflexivity. } assumption. Qed.
Hint Resolve context_derivative_sng : core.

Theorem context_derivative_comma: forall eta eta' g1 g2 g1' g2',
  DisjointSets (dom eta) (dom eta') ->
  ContextDerivative eta g1 g1' ->
  ContextDerivative eta' g2 g2' ->
  ContextDerivative (env_union eta eta') (CtxComma g1 g2) (CtxComma g1' g2').
Proof.
  intros. constructor; [| apply context_derivative_overwrite; assumption].
  apply context_derivative_noconflict; [| assumption].
  apply no_conflict_anywhere. apply disjoint_no_conflict. assumption.
Qed.
Hint Resolve context_derivative_comma : core.

Theorem context_derivative_semic: forall eta eta' g1 g2 g1' g2',
  DisjointSets (dom eta) (dom eta') ->
  ContextDerivative eta g1 g1' ->
  ContextDerivative eta' g2 g2' ->
  ContextDerivative (env_union eta eta') (CtxSemic g1 g2) (CtxSemic g1' g2').
Proof.
  intros. constructor; [| apply context_derivative_overwrite; assumption].
  apply context_derivative_noconflict; [| assumption].
  apply no_conflict_anywhere. apply disjoint_no_conflict. assumption.
Qed.
Hint Resolve context_derivative_semic : core.


Theorem fill_derivative : forall eta h d hd d_hd,
  Fill h d hd ->
  ContextDerivative eta hd d_hd ->
  exists d_h d_d,
    ContextDerivative eta d d_d /\
    HoleDerivative eta h d_h /\
    Fill d_h d_d d_hd /\
    (forall d0 d_d0 hd0 eta0,
      Fill h d0 hd0 ->
      NoConflictOn eta eta0 (fv h) -> (* a weaker condition here would likely suffice... *)
      ContextDerivative eta0 d0 d_d0 ->
      exists d_hd0, Fill d_h d_d0 d_hd0 /\ ContextDerivative (env_union eta eta0) hd0 d_hd0
    ).
Proof.
  intros.
  generalize dependent d_hd.
  generalize dependent eta.
  induction H; intros; [repeat econstructor; [assumption |];
    sinvert H; apply context_derivative_overwrite; assumption | | | |];
  sinvert H0; (edestruct IHFill as [d_h [d_d [A [B [C D]]]]]; [eassumption |]);
  eexists; eexists; (repeat split; [| constructor | constructor |]); try eassumption;
  intros; sinvert H0; (edestruct D as [d_hd0 [A' B']]; try eassumption; [
    intros x p p' Hx Ex Ex0; eapply H1; [right | |]; eassumption |]);
  eexists; (split; [constructor; eassumption |]); constructor; try assumption;
  (apply context_derivative_noconflict; [| assumption]);
  intros x p p' Hx Ex Ex0; (eapply H1; [left | |]); eassumption.
Qed.
Hint Resolve fill_derivative : core.

(* Theorem B.18 *)
Theorem maximal_derivative_nullable : forall p s s',
  Derivative p s s' ->
  MaximalPrefix p ->
  Nullable s'.
Proof.
  intros p s s' Hd Hm. generalize dependent s. generalize dependent s'.
  induction Hm; intros; sinvert Hd; try constructor; eauto.
Qed.
Hint Resolve maximal_derivative_nullable : core.

Theorem maximal_nullable' : forall p s s',
  Nullable s ->
  Derivative p s s' ->
  Nullable s'.
Proof.
  intros.
  generalize dependent s'. generalize dependent p.
  induction H; intros; sauto lq: on.
Qed.

Theorem maximal_derivative_nullable' : forall p s s',
  PrefixTyped p s ->
  Derivative p s s' ->
  Nullable s' ->
  MaximalPrefix p.
Proof.
intros p s s' Ht Hd Hn.
dependent induction Hd; sauto lq: on rew: off.
Qed.
Hint Resolve maximal_derivative_nullable : core.

Theorem maximal_context_derivative_nullable : forall eta g g',
  ContextDerivative eta g g' ->
  MaximalOn (fv g) eta ->
  NullableCtx g'.
Proof.
  intros eta g g' Hd.
  dependent induction Hd.
  - sfirstorder.
  - sauto use: maximal_derivative_nullable.
  - sfirstorder.
  - sfirstorder.
Qed.
Hint Resolve maximal_derivative_nullable : core.


Theorem maximal_context_derivative_nullable' : forall eta G G',
  EnvTyped eta G ->
  ContextDerivative eta G G' ->
  NullableCtx G' ->
  MaximalOn (fv G) eta.
Proof.
intros eta G G' Ht Hd Hn.
dependent induction Hd.
- sfirstorder.
- sauto use:maximal_derivative_nullable'.
- sauto lq: on rew: off.
- sauto lq: on rew: off.
Qed.



(* Theorem B.19 *)
Theorem nullable_prefix_empty : forall p s,
  PrefixTyped p s ->
  Nullable s ->
  p = emp s.
Proof.
  intros p s Ht Hn. generalize dependent p. induction Hn; intros; sinvert Ht. { reflexivity. }
  apply IHHn1 in H2. apply IHHn2 in H3. subst. reflexivity.
Qed.
Hint Resolve nullable_prefix_empty : core.


(* Fixpoint maybe_derivative p s : option type :=
  match p, s with
  | PfxEpsEmp, TyEps => Some TyEps
  | PfxOneEmp, TyOne => Some TyOne
  | PfxOneFull, TyOne => Some TyEps
  | PfxParPair p1 p2, TyPar s t =>
      match maybe_derivative p1 s, maybe_derivative p2 t with
      | Some a, Some b => Some (TyPar a b)
      | _, _ => None
      end
  | PfxCatFst p, TyDot s t => match maybe_derivative p s with Some s' => Some (TyDot s' t) | None => None end
  | PfxCatBoth p1 p2, TyDot s t => maybe_derivative p2 t
  | PfxSumEmp, TySum s t => Some (TySum s t)
  | PfxSumInl p, TySum s t => maybe_derivative p s
  | PfxSumInr p, TySum s t => maybe_derivative p t
  | PfxStarEmp, TyStar s => Some (TyStar s)
  | PfxStarDone, TyStar s => Some TyEps
  | PfxStarFirst p, TyStar s => match maybe_derivative p s with Some s' => Some (TyDot s' (TyStar s)) | None => None end
  | PfxStarRest p p', TyStar s => maybe_derivative p' (TyStar s)
  | _, _ => None
  end.

Theorem reflect_derivative : forall p s s',
  Derivative p s s' <-> maybe_derivative p s = Some s'.
Proof.
  split; intros.
  - induction H; cbn in *;
    try rewrite IHDerivative1;
    try rewrite IHDerivative2;
    try rewrite IHDerivative;
    reflexivity.
  - generalize dependent s. generalize dependent s'. induction p; intros;
    try solve [destruct s; sinvert H; constructor];
    destruct s; try discriminate H;
    cbn in *.
    + destruct (maybe_derivative p1 s1) eqn:E1; try discriminate H.
      destruct (maybe_derivative p2 s2) eqn:E2; try discriminate H.
      apply IHp1 in E1. apply IHp2 in E2.
      sinvert H. constructor; assumption.
    + destruct (maybe_derivative p s1) eqn:E; try discriminate H.
      apply IHp in E. sinvert H. constructor. assumption.
    + apply IHp2 in H. constructor. assumption.
    + apply IHp in H. constructor. assumption.
    + apply IHp in H. constructor. assumption.
    + destruct (maybe_derivative p s) eqn:E; try discriminate H.
      apply IHp in E. sinvert H. constructor. assumption.
    + apply IHp2 in H. constructor. assumption.
Qed.
Hint Resolve reflect_derivative : core.

Theorem reflect_no_derivative : forall p s,
  maybe_derivative p s = None ->
  ~exists s', Derivative p s s'.
Proof.
  intros p s H [s' C]. generalize dependent H. induction C; cbn; intros;
  try destruct (maybe_derivative p s);
  try destruct (maybe_derivative p1 s);
  try destruct (maybe_derivative p2 t);
  try solve [apply IHC; assumption];
  try solve [apply IHC1; assumption];
  try solve [apply IHC2; assumption];
  discriminate H.
Qed.
Hint Resolve reflect_no_derivative : core.

Definition derivative : forall p s, PrefixTyped p s -> type.
Proof.
  intros p s H. destruct (maybe_derivative p s) as [d |] eqn:E. { apply d. }
  apply derivative_fun in H.
  apply reflect_no_derivative in E.
  apply E in H. destruct H.
Qed. *)

(* TODO: will (use derivative_emp)*)

Theorem context_derivative_emp : forall g,
  WFContext g ->
  ContextDerivative (empty_env_for g) g g.
Proof.
  induction g; cbn in *; intros.
  - constructor.
  - econstructor. { cbn. rewrite eqb_refl. reflexivity. } apply derivative_emp.
  - sinvert H. apply context_derivative_comma; [| apply IHg1 | apply IHg2]; try assumption.
    intro x. split; intros Hx C; apply empty_env_for_dom in Hx; apply empty_env_for_dom in C;
    [apply H4 in C | apply H4 in Hx]; contradiction.
  - sinvert H. apply context_derivative_semic; [| apply IHg1 | apply IHg2]; try assumption.
    intro x. split; intros Hx C; apply empty_env_for_dom in Hx; apply empty_env_for_dom in C;
    [apply H4 in C | apply H4 in Hx]; contradiction.
Qed.

Theorem context_derivative_emp' : forall g g' eta,
  EmptyOn (fv g) eta ->
  ContextDerivative eta g g' ->
  g = g'.
Proof.
  induction g; intros.
  - sinvert H0. reflexivity.
  - cbn in H. specialize (H id (ltac:(auto))).
    edestruct H as [p [A B]].
    sinvert H0.
    destruct (ltac:(scongruence) : p = p0).
    sfirstorder use:derivative_emp'.
  - sinvert H0.
    assert (EmptyOn (fv g1) eta) by sfirstorder use:prop_on_set_union.
    assert (EmptyOn (fv g2) eta) by sfirstorder use:prop_on_set_union.
    hauto lq: on.
  - sinvert H0.
    assert (EmptyOn (fv g1) eta) by sfirstorder use:prop_on_set_union.
    assert (EmptyOn (fv g2) eta) by sfirstorder use:prop_on_set_union.
    hauto lq: on.
Qed.
Hint Resolve context_derivative_emp' : core.

Theorem context_derivative_subst_var_nop : forall D D' x y eta,
  ~ fv_ctx D x ->
  ContextDerivative eta D D' ->
  ContextDerivative (env_subst_var x y eta) D D'.
Proof.
  intros.
  generalize dependent x. generalize dependent y.
  induction H0; cbn in *; intros.
  - constructor.
  - econstructor; [| eassumption]. cbn. apply eqb_neq in H1. rewrite H1. assumption.
  - sfirstorder.
  - sfirstorder.
Qed.

(* Can also get away with this theorem having WFContext for D', Dxy, D'xy, etc. will also have a hole version. *)
Theorem context_derivative_subst_var : forall D D' x y eta Dxy D'xy,
  WFContext D ->
  WFContext Dxy ->
  CtxSubst x y D Dxy ->
  CtxSubst x y D' D'xy ->
  ContextDerivative eta D D' ->
  ContextDerivative (env_subst_var x y eta) Dxy D'xy.
Proof.
  intros.
  generalize dependent Dxy.
  generalize dependent D'xy.
  generalize dependent x.
  generalize dependent y.
  generalize dependent H.
  induction H3; intros.
  - sinvert H2.
  - sinvert H1. sinvert H2. sinvert H4. sinvert H3.
    econstructor; cbn. { rewrite eqb_refl. eassumption. } assumption.
  - sinvert H. sinvert H2; sinvert H1; sinvert H0.
    + econstructor. { apply IHContextDerivative1; assumption. }
      apply context_derivative_subst_var_nop; [| assumption].
      sauto use:ctx_subst_found_fv'.
    + assert (fv G' y) by sfirstorder use:ctx_subst_found_fv.
      assert (fv D y) by sfirstorder use:ctx_subst_found_fv.
      assert (fv G y) by hauto l: on use:fv_context_derivative.
      constructor; sfirstorder.
    + assert (fv G y) by sfirstorder use:ctx_subst_found_fv.
      assert (fv D' y) by sfirstorder use:ctx_subst_found_fv.
      assert (fv D y) by hauto l: on use:fv_context_derivative.
      constructor; sfirstorder.
    + econstructor.
      * eapply context_derivative_subst_var_nop; [| assumption].
        apply H9. eapply ctx_subst_found_fv'. eassumption.
      * apply IHContextDerivative2; assumption.
  - sinvert H. specialize (IHContextDerivative1 H5). specialize (IHContextDerivative2 H6).
    sinvert H2; sinvert H1; sinvert H0.
    + econstructor. { apply IHContextDerivative1; assumption. }
      eapply context_derivative_subst_var_nop; [| assumption].
      apply H9. eapply ctx_subst_found_fv'. eassumption.
    + apply ctx_subst_found_fv in H8. apply ctx_subst_found_fv in H4.
      apply fv_context_derivative in H3_. apply H3_ in H8. apply H7 in H4. apply H4 in H8 as [].
    + apply ctx_subst_found_fv in H8. apply ctx_subst_found_fv in H4.
      apply fv_context_derivative in H3_0. apply H3_0 in H8. apply H7 in H8. apply H8 in H4 as [].
    + constructor.
      * apply context_derivative_subst_var_nop; [| assumption].
        apply H9. eapply ctx_subst_found_fv'. eassumption.
      * apply IHContextDerivative2; assumption.
Qed.

Theorem derivative_ctx_subst : forall x y g dg dgxy eta,
  CtxSubst x y dg dgxy ->
  ContextDerivative eta g dg ->
  exists gxy, CtxSubst x y g gxy.
Proof.
  intros. edestruct (ctx_subst_exists x y g); [| eexists; eassumption].
  eapply fv_context_derivative. { eassumption. } eapply ctx_subst_found_fv. eassumption.
Qed.


(* Absolutely no idea how i came up with this one. just kept adding conclusions until we got what we needed, and then prayed it was true. *)

Theorem fill_derivative_ctx_subst : forall eta G D GD dGD x y dGDxy,
  Fill G D GD ->
  ContextDerivative eta GD dGD ->
  CtxSubst x y dGD dGDxy ->
  exists GDxy dD dG,
    CtxSubst x y GD GDxy /\
    ContextDerivative eta D dD /\
    HoleDerivative eta G dG /\
    Fill dG dD dGD /\
    ((exists Gxy dGxy , HoleSubst x y G Gxy /\ Fill Gxy D GDxy /\  HoleSubst x y dG dGxy /\ Fill dGxy dD dGDxy)
      \/
     (exists Dxy dDxy, CtxSubst x y D Dxy /\ Fill G Dxy GDxy /\ CtxSubst x y dD dDxy /\ Fill dG dDxy dGDxy)
    ).
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  generalize dependent dGDxy.
  generalize dependent G.
  generalize dependent D.
  induction H0; intros.
  - sinvert H1.
  - sinvert H1. sinvert H2. sauto lq: on rew: off.
  - sinvert H1; sinvert H.
    + sauto q: on.
    + sauto q: on.
    + sauto q: on use: fill_derivative.
    + sauto q: on.
    + sauto q: on use: fill_derivative.
    + sauto q: on.
  - sinvert H1; sinvert H.
    + sauto q: on.
    + sauto q: on.
    + sauto q: on use: fill_derivative.
    + sauto q: on.
    + sauto q: on use: fill_derivative.
    + sauto q: on.
Qed.
