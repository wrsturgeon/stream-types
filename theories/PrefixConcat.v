From Hammer Require Import Tactics.
From LambdaST Require Import
  Derivative
  Eqb
  Prefix
  Types.

(* Definition B.20 *)
Inductive PrefixConcat : prefix -> prefix -> prefix -> Prop :=
  | PfxCatEpsEmp :
      PrefixConcat PfxEpsEmp PfxEpsEmp PfxEpsEmp
  | PfxCatOneEmp : forall p,
      PrefixTyped p 1 ->
      PrefixConcat PfxOneEmp p p
  | PfxCatOneFull :
      PrefixConcat PfxOneFull PfxEpsEmp PfxOneFull
  | PfxCatParPair : forall p1 p1' p1'' p2 p2' p2'',
      PrefixConcat p1 p1' p1'' ->
      PrefixConcat p2 p2' p2'' ->
      PrefixConcat (PfxParPair p1 p2) (PfxParPair p1' p2') (PfxParPair p1'' p2'')
  | PfxCatCatFst : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxCatFst p) (PfxCatFst p') (PfxCatFst p'')
  | PfxCatCatFstCatBoth : forall p p' p'' p''',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxCatFst p) (PfxCatBoth p' p''') (PfxCatBoth p'' p''')
  | PfxCatCatBoth : forall p p' p'' p''',
      PrefixConcat p' p'' p''' ->
      PrefixConcat (PfxCatBoth p p') p'' (PfxCatBoth p p''')
  | PfxCatSumEmp : forall p,
      PrefixConcat PfxSumEmp p p
  | PfxCatSumInl : forall p p' p'',
      PrefixConcat p p' p'' -> (* <-- TODO: Was this a typo in the Appendix? *)
      PrefixConcat (PfxSumInl p) p' (PfxSumInl p'')
  | PfxCatSumInr : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxSumInr p) p' (PfxSumInr p'')
  | PfxCatStarEmp : forall p,
      PrefixConcat PfxStarEmp p p
  | PfxCatStarDone :
      PrefixConcat PfxStarDone PfxEpsEmp PfxStarDone
  | PfxCatStarFirst : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxStarFirst p) (PfxCatFst p') (PfxStarFirst p'')
  | PfxCatStarFirstStarRest : forall p p' p'' p''',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxStarFirst p) (PfxCatBoth p' p''') (PfxStarRest p'' p''')
  | PfxCatStarRest : forall p p' p'' p''',
      PrefixConcat p' p'' p''' ->
      PrefixConcat (PfxStarRest p p') p'' (PfxStarRest p p''')
  .
Hint Constructors PrefixConcat : core.

Fixpoint pfx_cat (arg_p arg_p' : prefix) : option prefix :=
  match arg_p, arg_p' with
  | PfxEpsEmp, PfxEpsEmp =>
      Some PfxEpsEmp
  | PfxOneEmp, p =>
      if pfx_ty p TyOne then Some p else None
  | PfxOneFull, PfxEpsEmp =>
      Some PfxOneFull
  | PfxParPair p1 p2, PfxParPair p1' p2' =>
      match pfx_cat p1 p1' with None => None | Some p1'' =>
      match pfx_cat p2 p2' with None => None | Some p2'' =>
      Some (PfxParPair p1'' p2'') end end
  | PfxCatFst p, PfxCatFst p' =>
      match pfx_cat p p' with None => None | Some p'' => Some (PfxCatFst p'') end
  | PfxCatFst p, PfxCatBoth p' p''' =>
      match pfx_cat p p' with None => None | Some p'' => Some (PfxCatBoth p'' p''') end
  | PfxCatBoth p p', p'' =>
      match pfx_cat p' p'' with None => None | Some p''' => Some (PfxCatBoth p p''') end
  | PfxSumEmp, p =>
      Some p
  | PfxSumInl p, p' =>
      match pfx_cat p p' with None => None | Some p'' => Some (PfxSumInl p'') end
  | PfxSumInr p, p' =>
      match pfx_cat p p' with None => None | Some p'' => Some (PfxSumInr p'') end
  | PfxStarEmp, p =>
      Some p
  | PfxStarDone, PfxEpsEmp =>
      Some PfxStarDone
  | PfxStarFirst p, PfxCatFst p' =>
      match pfx_cat p p' with None => None | Some p'' => Some (PfxStarFirst p'') end
  | PfxStarFirst p, PfxCatBoth p' p''' =>
      match pfx_cat p p' with None => None | Some p'' => Some (PfxStarRest p'' p''') end
  | PfxStarRest p p', p'' =>
      match pfx_cat p' p'' with None => None | Some p''' => Some (PfxStarRest p p''') end
  | _, _ => None
  end.
Arguments pfx_cat p p' : rename.

Theorem reflect_prefix_concat : forall p p' p'',
  pfx_cat p p' = Some p'' <-> PrefixConcat p p' p''.
Proof.
  split; intro H.
  - generalize dependent p'. generalize dependent p''. induction p; cbn in *; intros; sauto.
  - induction H; cbn in *; intros; sauto lq: on.
Qed.
Hint Resolve reflect_prefix_concat : core.

Theorem reflect_not_prefix_concat : forall p p',
  pfx_cat p p' = None <-> forall p'', ~PrefixConcat p p' p''.
Proof.
  intros. destruct (pfx_cat p p') eqn:E; split; intros.
  - discriminate H.
  - apply reflect_prefix_concat in E. apply H in E as [].
  - intro C. apply reflect_prefix_concat in C. rewrite E in C. discriminate C.
  - reflexivity.
Qed.
Hint Resolve reflect_not_prefix_concat : core.

Variant DecidePrefixConcat p p' :=
  | DecPfxCatY p'' (Y : PrefixConcat p p' p'')
  | DecPfxCatN (N : forall p'', ~PrefixConcat p p' p'')
  .

Theorem dec_pfx_cat : forall p p',
  DecidePrefixConcat p p'.
Proof.
  intros. destruct (pfx_cat p p') eqn:E.
  - eapply DecPfxCatY. apply reflect_prefix_concat. eassumption.
  - apply DecPfxCatN. apply reflect_not_prefix_concat. assumption.
Qed.

(* Theorem B.21, part I *)
Theorem pfx_cat_unique : forall p p' p1'' p2'',
  PrefixConcat p p' p1'' ->
  PrefixConcat p p' p2'' ->
  p1'' = p2''.
Proof.
  intros p p' p1'' p2'' H1 H2. apply reflect_prefix_concat in H1. apply reflect_prefix_concat in H2.
  rewrite H1 in H2. sinvert H2. reflexivity.
Qed.
Hint Resolve pfx_cat_unique : core.

Definition pfx_eqb_opt (a b : option prefix) :=
  match a, b with
  | None, None => true
  | Some a', Some b' => eqb a' b'
  | _, _ => false
  end.

Definition type_eqb_opt (a b : option type) :=
  match a, b with
  | None, None => true
  | Some a', Some b' => eqb a' b'
  | _, _ => false
  end.

Theorem maximal_prefix_concat : forall p p' p'',
  PrefixConcat p p' p'' ->
  MaximalPrefix p' ->
  forall t,
  PrefixTyped p'' t ->
  MaximalPrefix p''.
Proof.
  intros p p' p'' Hc Hm t Ht. generalize dependent p. generalize dependent p'.
  induction Ht; cbn in *; intros; try constructor; try assumption; sauto l: on.
Qed.

(* Theorem B.21, part II *)
Theorem pfx_cat_exists_when_typed : forall p p' s dps dp'dps,
  Derivative p s dps -> (* i.e., d_p(s) = `dps`. difficult to write in ASCII *)
  Derivative p' dps dp'dps -> (* i.e. d_{p'}(d_p(s)) = `dp'dps` *)
  PrefixTyped p s ->
  PrefixTyped p' dps ->
  exists p'',
  PrefixConcat p p' p'' /\ (* from "such a p'' exists" *)
  PrefixTyped p'' s /\
  Derivative p'' s dp'dps.
Proof.
  intros p p' s dps dp'dps Hd Hd' Hp Hp'. (* remember (pfx_cat p p') as reflected eqn:R. *)
  generalize dependent p'. generalize dependent dp'dps. generalize dependent Hp.
  induction Hd; intros.
  - sinvert Hp. sinvert Hd'. sinvert Hp'. eexists. repeat constructor.
  - sinvert Hp. eexists. split; [constructor | split]; assumption.
  - sinvert Hp. sinvert Hd'. sinvert Hp'. eexists. repeat constructor.
  - sinvert Hp. sinvert Hd'. sinvert Hp'.
    specialize (IHHd1 H2 _ _ H3 H5) as [p1'' [Hp1a [Hp1b Hp1c]]].
    specialize (IHHd2 H4 _ _ H6 H8) as [p2'' [Hp2a [Hp2b Hp2c]]].
    eexists. repeat constructor; eassumption.
  - (* DrvCatFst *)
    sinvert Hp. specialize (IHHd H1). sinvert Hd'; sinvert Hp'.
    + specialize (IHHd _ _ H4 H2) as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
    + assert (A := derivative_fun _ _ H5). destruct A as [p' H']. specialize (IHHd _ _ H' H5) as [p'' [Ha [Hb Hc]]].
      eexists. repeat split; constructor; try eassumption. eapply maximal_prefix_concat; eassumption.
  - sinvert Hp. specialize (IHHd H5 _ _ Hd' Hp') as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
  - sinvert Hp. eexists. repeat econstructor; eassumption.
  - sinvert Hp. specialize (IHHd H1 _ _ Hd' Hp') as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
  - sinvert Hp. specialize (IHHd H1 _ _ Hd' Hp') as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
  - sinvert Hp. eexists. repeat constructor; eassumption.
  - sinvert Hp. sinvert Hd'. sinvert Hp'. eexists. repeat constructor; eassumption.
  - sinvert Hp. specialize (IHHd H1). sinvert Hd'; sinvert Hp'.
    + specialize (IHHd _ _ H4 H2) as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
    + assert (A := derivative_fun _ _ H5). destruct A as [p' H']. specialize (IHHd _ _ H' H5) as [p'' [Ha [Hb Hc]]].
      eexists. repeat split; constructor; try eassumption. eapply maximal_prefix_concat; eassumption.
  - sinvert Hp. specialize (IHHd H4 _ _ Hd' Hp') as [p'' [Hp1 [Hp2 Hp3]]].
    eexists. repeat split; constructor; eassumption.
Qed.

(* Theorem B.22, part I *)
Theorem pfx_cat_empty_l : forall p s,
  PrefixTyped p s ->
  PrefixConcat (emp s) p p.
Proof. intros. induction H; sfirstorder. Qed.

(* Theorem B.22, part II *)
Theorem pfx_cat_empty_r : forall p s dps,
  Derivative p s dps ->
  PrefixTyped p s ->
  PrefixConcat p (emp dps) p.
Proof. intros p s dps Hd H. generalize dependent dps. induction H; sauto lq: on. Qed.

(* Theorem B.23, part I *)
Theorem max_pfx_concat_iff : forall p p' p'',
  PrefixConcat p p' p'' ->
  (MaximalPrefix p'' <-> (MaximalPrefix p \/ MaximalPrefix p'')).
Proof. intros. induction H; sauto lq: on. Qed.

(* Theorem B.23, part I *)
Theorem max_pfx_concat_eq : forall p p' p'',
  PrefixConcat p p' p'' ->
  MaximalPrefix p ->
  p = p''.
Proof. intros p p' p'' H. induction H; sauto lq: on rew: off. Qed.

Lemma pfx_cat_assoc : forall p q r s pq,
  PrefixConcat p q pq ->
  PrefixConcat pq r s ->
  exists qr, PrefixConcat p qr s /\ PrefixConcat q r qr.
Proof.
  intros p q r s pq Hl Hr. generalize dependent r. generalize dependent s. induction Hl; intros; (* sauto lq: on. *)
  try (sinvert H; sinvert Hr; eexists; repeat constructor; assumption);
  try (eexists; repeat constructor; assumption); sinvert Hr; try specialize (IHHl _ _ H0) as [qr1 [Hqr1 Hqr2]];
  try specialize (IHHl _ _ H3) as [qr [Hqr1 Hqr2]]; try (eexists; repeat constructor; eassumption).
  specialize (IHHl1 _ _ H1) as [qr1 [Hqr1l Hqr1r]]. specialize (IHHl2 _ _ H4) as [qr2 [Hqr2l Hqr2r]].
  eexists. repeat constructor; eassumption.
Qed.
Hint Resolve pfx_cat_assoc : core.

(* Theorem B.24 *)
(* NOTE: Joe, this is what you said you needed last time--it was a pretty easy corollary of the above *)
Lemma pfx_cat_assoc_eq : forall p q r pq qr s1 s2,
  PrefixConcat p q pq ->
  PrefixConcat q r qr ->
  PrefixConcat pq r s1 ->
  PrefixConcat p qr s2 ->
  s1 = s2.
Proof.
  intros p q r pq qr s1 s2 Hpq Hqr Hs1 Hs2.
  assert (A := pfx_cat_assoc _ _ _ _ _ Hpq Hs1). destruct A as [qr' [H1 H2]].
  assert (A := pfx_cat_unique _ _ _ _ Hqr H2). clear H2. symmetry in A. subst.
  assert (A := pfx_cat_unique _ _ _ _ Hs2 H1). subst. reflexivity.
Qed.
Hint Resolve pfx_cat_assoc_eq : core.
