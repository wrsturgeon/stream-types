From LambdaST Require Import
  Environment
  FV
  Ident
  Prefix
  Terms.

Inductive Step : env -> term -> term -> prefix -> Prop :=
  | S_Eps_R : forall n,
      Step n sink sink PfxEpsEmp
  | S_One_R : forall n,
      Step n unit sink PfxOneFull
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
      Step (subst x p (subst y (emp t) n)) e e' p' ->
      Step n (TmLetCat t x y z e) (TmLetCat t x y z e') p'
  .
(* TODO: FINISH DEFINITION *)
Hint Constructors Step : core.
