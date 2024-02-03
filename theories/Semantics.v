From Hammer Require Import Tactics.
From LambdaST Require Import
  Environment
  Prefix
  SinkTerm
  Subst
  Terms.

(* Definition B.44 *)
(* Meaning of (Step n e e' p) is
 *  "running the core term `e` on the input environment `n`
 *   yields the output prefix `p` and steps to `e'`."
 * Definition currently matches the one on page 9. *)
Inductive Step : env -> term -> term -> prefix -> Prop :=
  | SVar : forall n x p,
      n x = Some p ->
      Step n (TmVar x) (TmVar x) p
  | SParR : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      Step n e2 e2' p2 ->
      Step n (e1, e2) (e1', e2') (PfxParPair p1 p2)
  | SParL : forall n x y z e e' p1 p2 p',
      n z = Some (PfxParPair p1 p2) ->
      Step (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e e' p' ->
      Step n (TmLetPar x y z e) (TmLetPar x y z e') p'
  | SCatR1 : forall n e1 e1' e2 p,
      Step n e1 e1' p ->
      ~MaximalPrefix p ->
      Step n (e1; e2) (e1'; e2) (PfxCatFst p)
  | SCatR2 : forall n e1 e1' e2 e2' p1 p2,
      Step n e1 e1' p1 ->
      MaximalPrefix p1 ->
      Step n e2 e2' p2 ->
      Step n (e1; e2) e2' (PfxCatBoth p1 p2)
  | SCatL1 : forall t n x y z e e' p p',
      n z = Some (PfxCatFst p) ->
      Step (env_union n (env_union (singleton_env x p) (singleton_env y (emp t)))) e e' p' ->
      Step n (TmLetCat t x y z e) (TmLetCat t x y z e') p'
  | SCatL2 : forall t n x y z e e' p1 p2 p',
      n z = Some (PfxCatBoth p1 p2) ->
      Step (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e e' p' ->
      Step n (TmLetCat t x y z e) (TmLet x (sink_tm p1) (subst_var e z y)) p'
  | SEpsR : forall n,
      Step n TmSink TmSink PfxEpsEmp
  | SOneR : forall n,
      Step n TmUnit TmSink PfxOneFull
  | SCut : forall n x e1 e2 e1' e2' p p',
      Step n e1 e1' p ->
      Step (env_union n (singleton_env x p)) e2 e2' p' ->
      Step n (TmLet x e1 e2) (TmLet x e1' e2') p'
  .
Arguments Step n e e' p.
Hint Constructors Step : core.

(* Theorem B.48 *)
Theorem step_det : forall n e e' p',
  Step n e e' p' ->
  forall e'' p'',
  Step n e e'' p'' ->
  e' = e'' /\ p' = p''.
Proof.
  intros n e e' p' Hs e'' p'' Hs'. generalize dependent e''. generalize dependent p''.
  induction Hs; cbn in *; intros.
  - sinvert Hs'. sfirstorder.
  - sinvert Hs'. hauto lq: on rew: off.
  - sinvert Hs'. hauto l: on.
  - sinvert Hs'; sfirstorder.
  - sinvert Hs'. { sfirstorder. } sauto lq: on rew: off.
  - sinvert Hs'; [| scongruence]. hauto l: on.
  - sinvert Hs'. { scongruence. } hauto l: on.
  - sinvert Hs'. sfirstorder.
  - sinvert Hs'. sfirstorder.
  - sinvert Hs'. hauto lq: on.
Qed.
