From Coq Require Import String.
From LambdaST Require Import
  Context
  Environment
  Nullable
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
    (* On each variable, "call" the above inductive definition *)
  | HoleDrvHere : forall eta,
      HoleDerivative eta (CtxHasTy x s) (CtxHasTy x s')
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
  - exists t'. constructor. assumption.
  - exists s'. constructor. assumption.
  - exists s'. constructor. assumption.
  - exists (TyDot s' (TyStar s)). constructor. assumption.
  - exists t'. constructor. assumption.
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

Theorem context_derivative_emp' : forall g g' eta,
  EmptyOn (fv g) eta ->
  ContextDerivative eta g g' ->
  g = g'.
Proof.
induction g; intros.
- best.
- cbn in H. specialize (H id (ltac:(auto))).
  edestruct H as [p [A B]].
  sinvert H0.
  destruct (ltac:(scongruence) : p = p0).
  sfirstorder use:derivative_emp'.
- sinvert H0.
  assert (EmptyOn (fv g1) eta) by sfirstorder use:prop_on_union.
  assert (EmptyOn (fv g2) eta) by sfirstorder use:prop_on_union.
  hauto lq: on.
- sinvert H0.
  assert (EmptyOn (fv g1) eta) by sfirstorder use:prop_on_union.
  assert (EmptyOn (fv g2) eta) by sfirstorder use:prop_on_union.
  hauto lq: on.
Qed.

Hint Resolve derivative_emp : core.


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
