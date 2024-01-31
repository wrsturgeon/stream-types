From LambdaST Require Import
  Context
  Environment
  Nullable
  Prefix
  Types.
From Hammer Require Import Tactics.

Inductive Derivative : prefix -> type -> type -> Prop :=
  | DrvEpsEmp :
      Derivative PfxEpsEmp eps eps
  | DrvOneEmp :
      Derivative PfxOneEmp 1 1
  | DrvOneFull :
      Derivative PfxOneFull 1 eps
  | DrvParPair : forall p1 p2 s s' t t',
      Derivative p1 s s' ->
      Derivative p2 t t' ->
      Derivative (PfxParPair p1 p2) (TyPar s t) (TyPar s' t')
  | DrvCatFst : forall p s s' t,
      Derivative p s s' ->
      Derivative (PfxCatFst p) (TyDot s t) (TyDot s' t)
  | DrvCatBoth : forall p1 p2 s t t',
      Derivative p2 t t' ->
      Derivative (PfxCatBoth p1 p2) (TyDot s t) t'
  | DrvSumEmp : forall s t,
      Derivative PfxSumEmp (TySum s t) (TySum s t)
  | DrvSumInl : forall p s s' t,
      Derivative p s s' ->
      Derivative (PfxSumInl p) (TySum s t) s'
  (* TODO: this definition is almost certainly wrong in Appendix B *)
  | DrvSumInr : forall p s t t',
      Derivative p t t' ->
      Derivative (PfxSumInr p) (TySum s t) t'
  | DrvStarEmp : forall s,
      Derivative PfxStarEmp (TyStar s) (TyStar s)
  | DrvStarDone : forall s,
      Derivative PfxStarDone (TyStar s) eps
  | DrvStarFirst : forall p s s',
      Derivative p s s' ->
      Derivative (PfxStarFirst p) (TyStar s) (TyDot s' (TyStar s))
  | DrvStarRest : forall p p' s s',
      Derivative p' (TyStar s) s' ->
      Derivative (PfxStarRest p p') (TyStar s) s'
  .
Hint Constructors Derivative : core.

Inductive ContextDerivative : env -> context -> context -> Prop :=
  | CtxDrvEmpty : forall n,
      ContextDerivative n CtxEmpty CtxEmpty
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

(* Theorem B.15, part I *)
Theorem derivative_unique : forall p s s'1 s'2,
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
Hint Resolve derivative_unique : core.

(* Theorem B.15, part II *)
Theorem derivative_when_well_typed : forall p s,
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
Hint Resolve derivative_when_well_typed : core.

(* Theorem B.16 *)
Theorem derivative_emp : forall s,
  Derivative (emp s) s s.
Proof. induction s; cbn; constructor; assumption. Qed.
Hint Resolve derivative_emp : core.

(* Theorem B.17, part I *)
Theorem context_derivative_unique : forall n G G'1 G'2,
  ContextDerivative n G G'1 ->
  ContextDerivative n G G'2 ->
  G'1 = G'2.
Proof.
  intros n G G'1 G'2 H1 H2. generalize dependent G'2. induction H1; intros;
  sinvert H2; try (apply IHContextDerivative1 in H3; apply IHContextDerivative2 in H5; subst); try reflexivity.
  remember (maps_to_unique _ _ _ _ H H5) as U eqn:E. clear E. subst.
  remember (derivative_unique _ _ _ _ H0 H7) as U eqn:E. clear E. subst.
  reflexivity.
Qed.
Hint Resolve context_derivative_unique : core.

(* Theorem B.17, part II *)
Theorem derivative_when_env_well_typed : forall n G,
  EnvTyped n G ->
  exists G', ContextDerivative n G G'.
Proof.
  intros n G H. induction H;
  try (destruct IHEnvTyped1 as [G' HG]; destruct IHEnvTyped2 as [D' HD]);
  try (remember (derivative_when_well_typed p s H0) as D eqn:E; clear E; destruct D as [s' D]);
  eexists; econstructor; try apply H; try apply HG; try apply HD; apply D.
Qed.
Hint Resolve derivative_when_env_well_typed : core.

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

Fixpoint maybe_derivative p s : option type :=
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
  apply derivative_when_well_typed in H.
  apply reflect_no_derivative in E.
  apply E in H. destruct H.
Qed.
