From LambdaST Require Import
  Environment
  Prefix
  SinkTm
  Terms.

Inductive Step : env -> term -> term -> prefix -> Prop :=
  | S_Eps_R : forall n,
      Step n TmSink TmSink PfxEpsEmp
  | S_One_R : forall n,
      Step n TmUnit TmSink PfxOneFull
  | S_Var : forall n x p,
      n x = Some p ->
      Step n (TmVar x) (TmVar x) p
  | S_Par_R : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      Step n e2 e2' p2 ->
      Step n (e1, e2) (e1', e2') (PfxParPair p1 p2)
  | S_Cat_R_1 : forall n e1 e1' e2 p,
      Step n e1 e1' p ->
      ~MaximalPrefix p ->
      Step n (e1; e2) (e1'; e2) (PfxCatFst p)
  | S_Cat_R_2 : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      MaximalPrefix p1 ->
      Step n e2 e2' p2 ->
      Step n (e1; e2) e2' (PfxCatBoth p1 p2)
  | S_Par_L : forall n x y z e e' p1 p2 p',
      n z = Some (PfxParPair p1 p2) ->
      Step (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e e' p' ->
      Step n (TmLetPar x y z e) (TmLetPar x y z e') p'
  | S_Cat_L_1 : forall t n x y z e e' p p',
      n z = Some (PfxCatFst p) ->
      Step (env_union n (env_union (singleton_env x p) (singleton_env y (emp t)))) e e' p' ->
      Step n (TmLetCat t x y z e) (TmLetCat t x y z e') p'
  | S_Cat_L_2 : forall t n x y z e e' p1 p2 p',
      n z = Some (PfxCatBoth p1 p2) ->
      Step (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e e' p' ->
      Step n (TmLetCat t x y z e) (TmLet x (sink_tm p1) (subst_var e z y)) p'
  | S_Let : forall eta x e1 e2 e1' e2' p p',
      Step eta e1 e1' p ->
      Step (env_subst x p eta) e2 e2' p' ->
      Step eta (TmLet x e1 e2) (TmLet x e1' e2') p'
  | S_Drop : forall eta x e e' p,
      Step (env_drop eta x) e e' p ->
      Step eta (TmDrop x e) (TmDrop x e') p
  .
(* TODO: FINISH DEFINITION *)
Hint Constructors Step : core.
