From LambdaST Require Import
  Environment
  Prefix
  Terms.


Inductive Step : env -> term -> term -> prefix -> Prop :=
  | S_Eps_R : forall n,
      Step n sink sink PfxEpsEmp
  | S_One_R : forall n,
      Step n unit sink PfxOneFull
  | S_Var : forall n x p,
      MapsTo p x n ->
      Step n (TmVar x) (TmVar x) p
  | S_Par_R : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      Step n e2 e2' p2 ->
      Step n (e1, e2) (e1', e2') (PfxParPair p1 p2)
  | S_Cat_R_1 : forall n e1 e1' e2 p,
      Step n e1 e1' p ->
      ~Maximal p ->
      Step n (e1; e2) (e1'; e2) (PfxCatFst p)
  | S_Cat_R_2 : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      Maximal p1 ->
      Step n e2 e2' p2 ->
      Step n (e1; e2) e2' (PfxCatBoth p1 p2)
  | S_Par_L : forall n x y z e e' p1 p2 p',
      MapsTo (PfxParPair p1 p2) z n ->
      Step (subst x p1 (subst y p2 n)) e e' p' ->
      Step n (TmLetPar x y z e) (TmLetPar x y z e') p'
  | S_Cat_L_1 : forall t n x y z e e' p p',
      MapsTo (PfxCatFst p) z n ->
      Step (subst x p (subst y (emp t) n)) e e' p' ->
      Step n (TmLetCat t x y z e) (TmLetCat t x y z e') p'
  .

Print Step.

