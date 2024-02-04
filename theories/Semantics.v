
From LambdaST Require Import
  Environment
  Prefix
  SinkTerm
  Subst
  Context
  FV
  Derivative
  Terms.

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
      Step n (TmLetCat t x y z e) (TmLet x (sink_tm p1) (subst_var e z y)) p'
  | SLet : forall eta x e1 e2 e1' e2' p p',
      Step eta e1 e1' p ->
      Step (env_subst x p eta) e2 e2' p' ->
      Step eta (TmLet x e1 e2) (TmLet x e1' e2') p'
with
ArgsStep : env -> context -> argsterm -> argsterm -> context -> env -> Prop :=
  | SATmEmpty : forall eta,
        ArgsStep eta CtxEmpty ATmEmpty ATmEmpty CtxEmpty empty_env
  | SATmSng : forall eta x s s' e e' p,
        Step eta e e' p ->
        Derivative p s s' ->
        ArgsStep eta (CtxHasTy x s) (ATmSng e) (ATmSng e') (CtxHasTy x s') (singleton_env x p)
  | SATmComma : forall eta g1 g1' g2 g2' e1 e2 e1' e2' eta1 eta2,
        ArgsStep eta g1 e1 e1' g1' eta1 ->
        ArgsStep eta g2 e2 e2' g2' eta2 ->
        ArgsStep eta (CtxComma g1 g2) (ATmComma e1 e2) (ATmComma e1' e2') (CtxComma g1' g2') (env_union eta1 eta2)
  | SATmSemic1 : forall eta g1 g1' g2 e1 e2 e1' eta1,
        ArgsStep eta g1 e1 e1' g1' eta1 ->
        ~(MaximalOn (fv g1) eta1) ->
        ArgsStep eta (CtxSemic g1 g2) (ATmSemic e1 e2) (ATmSemic e1' e2) (CtxSemic g1' g2) (env_union eta1 (empty_env_for g2))
  | SATmSemic2 : forall eta g1 g1' g2 g2' e1 e2 e1' e2' eta1 eta2,
        ArgsStep eta g1 e1 e1' g1' eta1 ->
        MaximalOn (fv g1) eta1 ->
        ArgsStep eta g2 e2 e2' g2' eta2 ->
        ArgsStep eta (CtxSemic g1 g2) (ATmSemic e1 e2) (ATmSemic e1' e2') (CtxSemic g1' g2') (env_union eta1 eta2)
.

Theorem Step_det : forall eta e e1 e2 p1 p2,
    Step eta e e1 p1 ->
    Step eta e e2 p2 ->
    e1 = e2 /\ p1 = p2
.
Proof.
Admitted.


(* evalArgs (SemicCtx g1 g2) (SemicCtx e1 e2) = do
    (env1,g1',e1') <- evalArgs g1 e1
    if env1 `maximalOn` g1 then do
        (env2,g2',e2') <- evalArgs g2 e2
        env <- reThrow (\(x,p,p') -> UnionEnvError x p p') (unionDisjointEnv env1 env2)
        return (env,SemicCtx g1' g2', SemicCtx e1' e2')
    else do
        let env2 = emptyEnvFor g2
        env <- reThrow (\(x,p,p') -> UnionEnvError x p p') (unionDisjointEnv env1 env2)
        return (env,SemicCtx g1' g2, SemicCtx e1' e2)
        where
            env `maximalOn` g = all (\(CE x _) -> isJust (lookupEnv x env >>= Values.maximalLift)) g
            emptyEnvFor g = foldr (\(CE x s) rho -> bindEnv x (emptyPrefix s) rho) emptyEnv g *)


(* TODO: FINISH DEFINITION *)
Arguments Step n e e' p.
Hint Constructors Step : core.
