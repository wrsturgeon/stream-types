From LambdaST Require Import
  Context
  Environment
  Invert
  Nullable
  Prefix
  Types.

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
  (* TODO: his definition is almost certainly wrong in Appendix B *)
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

Inductive ContextDerivative : env -> context -> context -> Prop :=
  | CtxDrvEmpty : forall n,
      ContextDerivative n CtxEmpty CtxEmpty
  | CtxDrvHasTy : forall n x p s s',
      MapsTo p x n ->
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

(* Theorem B.15, part I *)
Theorem derivative_unique : forall p s s'1 s'2,
  Derivative p s s'1 ->
  Derivative p s s'2 ->
  s'1 = s'2.
Proof.
  intros p s s'1 s'2 H1 H2. generalize dependent s'2. induction H1; intros;
  invert H2; try reflexivity; auto.
  - apply IHDerivative1 in H5. apply IHDerivative2 in H6. subst. reflexivity.
  - apply IHDerivative in H5. subst. reflexivity.
  - apply IHDerivative in H3. subst. reflexivity.
Qed.

(* Theorem B.15, part II *)
Theorem derivative_when_well_typed : forall p s,
  PfxTyped p s ->
  exists s', Derivative p s s'.
Proof.
  intros p s H. induction H; try solve [eexists; constructor];
  try destruct IHPfxTyped as [s' Hd];
  try destruct IHPfxTyped1 as [s' Hd1];
  try destruct IHPfxTyped2 as [t' Hd2].
  - exists (TyPar s' t'). constructor; assumption.
  - exists (TyDot s' t). constructor. assumption.
  - exists t'. constructor. assumption.
  - exists s'. constructor. assumption.
  - exists s'. constructor. assumption.
  - exists (TyDot s' (TyStar s)). constructor. assumption.
  - exists t'. constructor. assumption.
Qed.

(* Theorem B.16 *)
Theorem derivative_emp : forall s,
  Derivative (emp s) s s.
Proof. induction s; simpl; constructor; assumption. Qed.

(* Theorem B.17, part I *)
Theorem context_derivative_unique : forall n G G'1 G'2,
  ContextDerivative n G G'1 ->
  ContextDerivative n G G'2 ->
  G'1 = G'2.
Proof.
  intros n G G'1 G'2 H1 H2. generalize dependent G'2. induction H1; intros;
  invert H2; try (apply IHContextDerivative1 in H3; apply IHContextDerivative2 in H5; subst); try reflexivity.
  remember (maps_to_unique _ _ _ _ H H5) as U eqn:E. clear E. subst.
  remember (derivative_unique _ _ _ _ H0 H7) as U eqn:E. clear E. subst.
  reflexivity.
Qed.

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

(* Theorem B.18 *)
Theorem maximal_derivative_nullable : forall p s s',
  Derivative p s s' ->
  Maximal p ->
  Nullable s'.
Proof.
  intros p s s' Hd Hm. generalize dependent s. generalize dependent s'.
  induction Hm; intros; invert Hd; try constructor; eauto.
Qed.

(* Theorem B.19 *)
Theorem nullable_prefix_empty : forall p s,
  PfxTyped p s ->
  Nullable s ->
  p = emp s.
Proof.
  intros p s Ht Hn. generalize dependent p. induction Hn; intros; invert Ht. { reflexivity. }
  apply IHHn1 in H2. apply IHHn2 in H3. subst. reflexivity.
Qed.
