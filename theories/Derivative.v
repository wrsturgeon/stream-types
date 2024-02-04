From LambdaST Require Import
  Context
  Environment
  FV
  Nullable
  Prefix
  Sets
  Types.
From Hammer Require Import Tactics.

(* Definition B.13 *)
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
Arguments Derivative p s s'.
Hint Constructors Derivative : core.

Definition B13 := Derivative.
Arguments B13/ p s s'.

Fixpoint derivative (arg_p : prefix) (arg_s : type) : option type :=
  match arg_p, arg_s with
  | PfxEpsEmp, TyEps =>
      Some TyEps
  | PfxOneEmp, TyOne =>
      Some TyOne
  | PfxOneFull, TyOne =>
      Some TyEps
  | PfxParPair p1 p2, TyPar s t =>
      match derivative p1 s with None => None | Some s' =>
      match derivative p2 t with None => None | Some t' =>
      Some (TyPar s' t') end end
  | PfxCatFst p, TyDot s t =>
      match derivative p s with None => None | Some s' => Some (TyDot s' t) end
  | PfxCatBoth p1 p2, TyDot s t =>
      derivative p2 t
  | PfxSumEmp, TySum s t =>
      Some (TySum s t)
  | PfxSumInl p, TySum s t =>
      derivative p s
  | PfxSumInr p, TySum s t =>
      derivative p t
  | PfxStarEmp, TyStar s =>
      Some (TyStar s)
  | PfxStarDone, TyStar s =>
      Some TyEps
  | PfxStarFirst p, TyStar s =>
      match derivative p s with None => None | Some s' => Some (TyDot s' (TyStar s)) end
  | PfxStarRest p p', TyStar s =>
      derivative p' (TyStar s)
  | _, _ => None
  end.
Arguments derivative p s : rename.

Theorem reflect_derivative : forall p s s',
  derivative p s = Some s' <-> Derivative p s s'.
Proof.
  split; intro H.
  - generalize dependent s. generalize dependent s'. induction p; hauto drew: off.
  - induction H; qauto l: on.
Qed.
Hint Resolve reflect_derivative : core.

Theorem reflect_not_derivative : forall p s,
  derivative p s = None <-> forall s', ~Derivative p s s'.
Proof.
  intros. split; intros.
  - intro C. apply reflect_derivative in C. rewrite H in C. discriminate C.
  - destruct (derivative p s) eqn:E; [| reflexivity]. apply reflect_derivative in E. apply H in E as [].
Qed.
Hint Resolve reflect_not_derivative : core.

Variant DecideDerivative p s :=
  | DecDerivY s' (Y : Derivative p s s')
  | DecDerivN (N : forall s', ~Derivative p s s')
  .

Theorem dec_deriv : forall p s,
  DecideDerivative p s.
Proof.
  intros. destruct (derivative p s) eqn:E.
  - eapply DecDerivY. apply reflect_derivative. eassumption.
  - apply DecDerivN. apply reflect_not_derivative. assumption.
Qed.

(* Theorem B.15, part I *)
Theorem derivative_det : forall p s s'1 s'2,
  Derivative p s s'1 ->
  Derivative p s s'2 ->
  s'1 = s'2.
Proof.
  intros p s s'1 s'2 H1 H2. apply reflect_derivative in H1. apply reflect_derivative in H2.
  rewrite H1 in H2. sinvert H2. reflexivity.
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

Definition B15 := derivative_fun.
Arguments B15/.

(* Theorem B.16 *)
Theorem derivative_emp : forall s,
  Derivative (emp s) s s.
Proof. induction s; cbn; constructor; assumption. Qed.
Hint Resolve derivative_emp : core.

Definition B16 := derivative_emp.
Arguments B16/.

(* Definition B.14 *)
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
Arguments ContextDerivative n G G'.
Hint Constructors ContextDerivative : core.

Definition B14 := ContextDerivative.
Arguments B14/ n G G'.

Fixpoint ctx_derivative (n : env) (arg_G : context) : option context :=
  match arg_G with
  | CtxEmpty =>
      Some CtxEmpty
  | CtxHasTy x s =>
      match n x with None => None | Some p =>
      match derivative p s with None => None | Some s' =>
      Some (CtxHasTy x s') end end
  | CtxComma G D =>
      match ctx_derivative n G with None => None | Some G' =>
      match ctx_derivative n D with None => None | Some D' =>
      Some (CtxComma G' D') end end
  | CtxSemic G D =>
      match ctx_derivative n G with None => None | Some G' =>
      match ctx_derivative n D with None => None | Some D' =>
      Some (CtxSemic G' D') end end
  end.
Arguments ctx_derivative n G : rename.

Theorem reflect_ctx_derivative : forall n G G',
  ctx_derivative n G = Some G' <-> ContextDerivative n G G'.
Proof.
  split; intro H.
  - generalize dependent n. generalize dependent G'. induction G; cbn in *; intros.
    + sinvert H. constructor.
    + destruct (n id) eqn:E; [| discriminate H]. destruct (derivative p ty) eqn:D; [| discriminate H].
      sinvert H. assert (Hd := D). apply reflect_derivative in Hd. econstructor; eassumption.
    + destruct (ctx_derivative n G1) eqn:E1; [| discriminate H].
      destruct (ctx_derivative n G2) eqn:E2; sinvert H.
      apply IHG1 in E1. apply IHG2 in E2. econstructor; eassumption.
    + destruct (ctx_derivative n G1) eqn:E1; [| discriminate H].
      destruct (ctx_derivative n G2) eqn:E2; sinvert H.
      apply IHG1 in E1. apply IHG2 in E2. econstructor; eassumption.
  - induction H; cbn in *.
    + reflexivity.
    + rewrite H. apply reflect_derivative in H0. rewrite H0. reflexivity.
    + rewrite IHContextDerivative1. rewrite IHContextDerivative2. reflexivity.
    + rewrite IHContextDerivative1. rewrite IHContextDerivative2. reflexivity.
Qed.
Hint Resolve reflect_ctx_derivative : core.

Theorem reflect_not_ctx_derivative : forall n G,
  ctx_derivative n G = None <-> forall G', ~ContextDerivative n G G'.
Proof.
  intros. split; intros.
  - intro C. apply reflect_ctx_derivative in C. rewrite H in C. discriminate C.
  - destruct (ctx_derivative n G) eqn:E; [| reflexivity]. apply reflect_ctx_derivative in E. apply H in E as [].
Qed.
Hint Resolve reflect_not_ctx_derivative : core.

Variant DecideContextDerivative n G :=
  | DecCtxDerivY G' (Y : ContextDerivative n G G')
  | DecCtxDerivN (N : forall G', ~ContextDerivative n G G')
  .

Theorem dec_ctx_deriv : forall n G,
  DecideContextDerivative n G.
Proof.
  intros. destruct (ctx_derivative n G) eqn:E.
  - eapply DecCtxDerivY. apply reflect_ctx_derivative. eassumption.
  - apply DecCtxDerivN. apply reflect_not_ctx_derivative. assumption.
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

Definition B17 := context_derivative_fun.
Arguments B17/.

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

Definition B18 := maximal_derivative_nullable.
Arguments B18/.

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

Definition B19 := nullable_prefix_empty.
Arguments B19/.

Theorem ctx_deriv_fv : forall n G G',
  ContextDerivative n G G' ->
  SetEq (fv G) (fv G').
Proof. intros. induction H; sfirstorder. Qed.
Hint Resolve ctx_deriv_fv : core.
