From Hammer Require Import Tactics.
From LambdaST Require Import
  Environment
  Prefix
  SinkTerm
  Subst
  Context
  FV
  Derivative
  PrefixConcat
  History
  Terms.


(* 
(4?) star-case
*)

Inductive Step : env -> term -> term -> prefix -> Prop :=
  | SEpsR : forall n,
      Step n TmSink TmSink PfxEpsEmp
  | SOneR : forall n,
      Step n TmUnit TmSink PfxOneFull
  | SVar : forall n x p,
      n x = Some p ->
      Step n (TmVar x) (TmVar x) p
  | SParR : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      Step n e2 e2' p2 ->
      Step n (e1, e2) (e1', e2') (PfxParPair p1 p2)
  | SCatR1 : forall n e1 e1' e2 p,
      Step n e1 e1' p ->
      ~MaximalPrefix p ->
      Step n (e1; e2) (e1'; e2) (PfxCatFst p)
  | SCatR2 : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      MaximalPrefix p1 ->
      Step n e2 e2' p2 ->
      Step n (e1; e2) e2' (PfxCatBoth p1 p2)
  | SParL : forall n x y z e e' p1 p2 p',
      n z = Some (PfxParPair p1 p2) ->
      Step (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e e' p' ->
      Step n (TmLetPar x y z e) (TmLetPar x y z e') p'
  | SCatL1 : forall t n x y z e e' p p',
      n z = Some (PfxCatFst p) ->
      Step (env_union n (env_union (singleton_env x p) (singleton_env y (emp t)))) e e' p' ->
      Step n (TmLetCat t x y z e) (TmLetCat t x y z e') p'
  | SCatL2 : forall t n x y z e e' p1 p2 p',
      n z = Some (PfxCatBoth p1 p2) ->
      Step (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e e' p' ->
      Step n (TmLetCat t x y z e) (TmLet x (sink_tm p1) (subst_var e' z y)) p'
  | SLet : forall eta x e1 e2 e1' e2' p p',
      Step eta e1 e1' p ->
      Step (env_subst x p eta) e2 e2' p' ->
      Step eta (TmLet x e1 e2) (TmLet x e1' e2') p'
  | SInl : forall eta e e' p,
        Step eta e e' p ->
        Step eta (TmInl e) e' (PfxSumInl p)
  | SInr : forall eta e e' p,
        Step eta e e' p ->
        Step eta (TmInr e) e' (PfxSumInr p)
  | SPlusCase1 : forall eta eta' eta'' r z x y e1 e2,
        EnvConcat eta' eta eta'' ->
        eta'' z = Some PfxSumEmp ->
        Step eta (TmPlusCase eta' r z x e1 y e2) (TmPlusCase eta'' r z x e1 y e2) (emp r)
  | SPlusCase2 : forall eta eta' eta'' r z x y e1 e2 e' p p',
        EnvConcat eta' eta eta'' ->
        eta'' z = Some (PfxSumInl p) ->
        Step (env_union eta'' (singleton_env x p)) e1 e' p' ->
        Step eta (TmPlusCase eta' r z x e1 y e2) (subst_var e' z x) p'
  | SPlusCase3 : forall eta eta' eta'' r z x y e1 e2 e' p p',
        EnvConcat eta' eta eta'' ->
        eta'' z = Some (PfxSumInr p) ->
        Step (env_union eta'' (singleton_env y p)) e2 e' p' ->
        Step eta (TmPlusCase eta' r z x e1 y e2) (subst_var e' z y) p'
  | SNil : forall eta,
        Step eta TmNil TmSink PfxStarDone
  | SCons1 : forall n e1 e1' e2 p,
      Step n e1 e1' p ->
      ~MaximalPrefix p ->
      Step n (TmCons e1 e2) (e1'; e2) (PfxStarFirst p)
  | SCons2 : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      MaximalPrefix p1 ->
      Step n e2 e2' p2 ->
      Step n (TmCons e1 e2) e2' (PfxStarRest p1 p2)
  | SFix : forall eta eta' g g' args args' e e' r p hpargs vs,
      HistArgsStep hpargs vs ->
      ArgsStep eta  g args args' g' eta' ->
      Step eta' (histval_subst_all vs (fix_subst g r e e)) e' p ->
      Step eta (TmFix args hpargs g r e) (TmArgsLet args' g' e') p
  | SArgsLet : forall eta eta' g g' args args' e e' p,
        ArgsStep eta g args args' g' eta' ->
        Step eta' e e' p ->
        Step eta (TmArgsLet args g e) (TmArgsLet args' g' e') p
  | SHistPgm : forall hp s v p eta,
        HistStep hp v ->
        HistValLift s v p ->
        Step eta (TmHistPgm hp s) (sink_tm p) p
  | SWait1 : forall eta eta' eta'' z p s r e,
        EnvConcat eta' eta eta'' ->
        eta'' z = Some p ->
        ~(MaximalPrefix p) ->
        Step eta (TmWait eta' r s z e) (TmWait eta'' r s z e) (emp r)
  | SWait2 : forall eta eta' eta'' z p p' s r e e' v,
        EnvConcat eta' eta eta'' ->
        eta'' z = Some p ->
        MaximalPrefix p ->
        PrefixFlatten p v ->
        Step eta'' (histval_subst v 0 e) e' p' ->
        Step eta (TmWait eta' r s z e) e' p'
with ArgsStep : env -> context -> argsterm -> argsterm -> context -> env -> Prop :=
  | ASEmpty : forall eta,
        ArgsStep eta CtxEmpty ATmEmpty ATmEmpty CtxEmpty empty_env
  | ASSng : forall eta x s s' e e' p,
        Step eta e e' p ->
        Derivative p s s' ->
        ArgsStep eta (CtxHasTy x s) (ATmSng e) (ATmSng e') (CtxHasTy x s') (singleton_env x p)
  | ASComma : forall eta g1 g1' g2 g2' e1 e2 e1' e2' eta1 eta2,
        ArgsStep eta g1 e1 e1' g1' eta1 ->
        ArgsStep eta g2 e2 e2' g2' eta2 ->
        ArgsStep eta (CtxComma g1 g2) (ATmComma e1 e2) (ATmComma e1' e2') (CtxComma g1' g2') (env_union eta1 eta2)
  | ASSemic11 : forall eta g1 g1' g2 e1 e2 e1' eta1,
        ArgsStep eta g1 e1 e1' g1' eta1 ->
        ~(MaximalOn (fv g1) eta1) ->
        ArgsStep eta (CtxSemic g1 g2) (ATmSemic1 e1 e2) (ATmSemic1 e1' e2) (CtxSemic g1' g2) (env_union eta1 (empty_env_for g2))
  | ASSemic12 : forall eta g1 g1' g2 g2' e1 e2 e1' e2' eta1 eta2,
        ArgsStep eta g1 e1 e1' g1' eta1 ->
        MaximalOn (fv g1) eta1 ->
        ArgsStep eta g2 e2 e2' g2' eta2 ->
        ArgsStep eta (CtxSemic g1 g2) (ATmSemic1 e1 e2) (ATmSemic2 e2') (CtxSemic g1' g2') (env_union eta1 eta2)
  | ASSemic2 : forall eta g1 g2 g2' e2 e2' eta2,
        ArgsStep eta g2 e2 e2' g2' eta2 ->
        ArgsStep eta (CtxSemic g1 g2) (ATmSemic2 e2) (ATmSemic2 e2') (CtxSemic g1 g2') (env_union (empty_env_for g1) eta2)
  .

Hint Constructors Step : core.
Hint Constructors ArgsStep : core.
Arguments Step n e e' p.

Scheme Step_ind' := Induction for Step Sort Prop
with ArgsStep_ind' := Induction for ArgsStep Sort Prop.
Combined Scheme Step_mutual from Step_ind', ArgsStep_ind'.

(* TODO:will eta eta', agree on fv e *)
Theorem step_det : forall eta e e1 e2 p1 p2,
    Step eta e e1 p1 ->
    Step eta e e2 p2 ->
    e1 = e2 /\ p1 = p2.
Proof.
  intros. generalize dependent e2. generalize dependent p2. induction H; cbn in *; intros.
  - sinvert H0. repeat constructor.
  - sinvert H0. repeat constructor.
  - sinvert H0. rewrite H in H3. sinvert H3. repeat constructor.
  - sinvert H1. specialize (IHStep1 _ _ H5) as [Ee1 Ep1].
    specialize (IHStep2 _ _ H8) as [Ee2 Ep2]. subst. repeat constructor.
  - sinvert H1. { specialize (IHStep _ _ H5) as [Ee Ep]. subst. repeat constructor. }
    specialize (IHStep _ _ H4) as [Ee Ep]. subst. apply H0 in H6 as [].
  - sinvert H2. { specialize (IHStep1 _ _ H6) as [Ee Ep]. subst. apply H9 in H0 as []. }
    specialize (IHStep1 _ _ H5) as [Ee1 Ep1]. specialize (IHStep2 _ _ H10) as [Ee2 Ep2].
    subst. repeat constructor.
  - sinvert H1. rewrite H in H9. sinvert H9. specialize (IHStep _ _ H10) as [Ee Ep].
    subst. repeat constructor.
  - sinvert H1; rewrite H in H10; sinvert H10.
    specialize (IHStep _ _ H11) as [Ee Ep]. subst. repeat constructor.
  - sinvert H1; rewrite H in H10; sinvert H10.
    specialize (IHStep _ _ H11) as [Ee Ep]. subst. repeat constructor.
  - sinvert H1. specialize (IHStep1 _ _ H8) as [Ee Ep]. subst.
    edestruct IHStep2 as [Ee Ep]; [| split; f_equal]; eassumption.
  - sauto lq: on rew: off.
  - sauto lq: on rew: off.
  - sinvert H1; assert (A := env_cat_unique _ _ _ _ H H12); subst; [repeat constructor | |]; congruence.
  - sinvert H2; assert (A := env_cat_unique _ _ _ _ H H13); subst; [congruence | | congruence].
    assert (p = p0) by congruence. subst. specialize (IHStep _ _ H15) as [Ee Ep]. subst. sfirstorder.
  - sinvert H2; assert (A := env_cat_unique _ _ _ _ H H13); subst; [congruence | congruence |].
    assert (p = p0) by congruence. subst. specialize (IHStep _ _ H15) as [Ee Ep]. subst. sfirstorder.
  - admit.
Admitted.
Hint Resolve step_det : core.

Theorem step_bv :
      (forall eta e e' p, Step eta e e' p -> forall x, bv_term e' x -> bv_term e x) /\
      (forall eta g e e' g' eta', ArgsStep eta g e e' g' eta' -> forall x, bv_argsterm e' x -> bv_argsterm e x).
Proof.
apply Step_mutual; intros.
- best.
- best.
- best.
- best.
- best.
- best.
- best.
- best.
- cbn. cbn in H0. best use:bv_sinktm.
- best.
- best.
- best.
- best.
- best use:bv_var_subst.
- best use:bv_var_subst.
- best.
- best.
- best.
- best.
- best.
- best use:bv_sinktm.
- best.
- best use:bv_histval_subst.
- best.
- best.
- best.
- best.
- best.
- best.
Qed.