Require Import Coq.Program.Equality.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Derivative
  Prefix
  Environment
  FV
  Context
  Sets
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
      MaximalPrefix p ->
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
      MaximalPrefix p ->
      PrefixConcat (PfxStarRest p p') p'' (PfxStarRest p p''')
  .
Hint Constructors PrefixConcat : core.
(* Theorem B.21, part I *)
Theorem pfx_cat_unique : forall p p' p1'' p2'',
  PrefixConcat p p' p1'' ->
  PrefixConcat p p' p2'' ->
  p1'' = p2''.
Proof.
  intros p p' p1'' p2'' H1 H2. generalize dependent p2''. induction H1; intros; sinvert H2;
  try apply IHPrefixConcat in H3;
  try apply IHPrefixConcat in H5;
  try apply IHPrefixConcat in H0;
  subst; try reflexivity.
  f_equal; [apply IHPrefixConcat1 | apply IHPrefixConcat2]; assumption.
  sfirstorder. sfirstorder.
Qed.
Hint Resolve pfx_cat_unique : core.

Theorem pfx_cat_maximal : forall p p' p'',
  PrefixConcat p p' p'' ->
  MaximalPrefix p \/ MaximalPrefix p' -> MaximalPrefix p''.
Proof. intros. induction H; sauto lq: on. Qed.
Hint Resolve pfx_cat_maximal : core.
  
(* partial converse: if p . p' is maximal, than p' must be. *)
Theorem pfx_cat_maximal' : forall p p' p'',
  PrefixConcat p p' p'' ->
  MaximalPrefix p'' -> MaximalPrefix p'.
Proof. intros. generalize dependent H0. induction H; sauto lq: on rew: off. Qed.
Hint Resolve pfx_cat_maximal' : core.

Theorem pfx_cat_maximal'' : forall p,
  MaximalPrefix p ->
  exists p', PrefixConcat p p' p /\ EmptyPrefix p'.
Proof. intros. induction H; sauto lq: on. Qed.
Hint Resolve pfx_cat_maximal'' : core.

Theorem pfx_cat_maximal''' : forall p p' p'', MaximalPrefix p -> PrefixConcat p p' p'' -> p = p''.
Proof. intros. generalize dependent p'. generalize dependent p''. induction H; sauto lq: on rew: off. Qed.
Hint Resolve pfx_cat_maximal''' : core.

Theorem pfx_cat_empty : forall p p' p'',
  PrefixConcat p p' p'' ->
  EmptyPrefix p /\ EmptyPrefix p' <-> EmptyPrefix p''.
Proof. intros. induction H; sauto lq: on rew: off. Qed.
Hint Resolve pfx_cat_empty : core.

(* Theorem B.21, part II *)
Theorem pfx_cat_exists_when_typed : forall p p' s dps,
  Derivative p s dps -> (* i.e., d_p(s) = `dps`. difficult to write in ASCII *)
  PrefixTyped p s ->
  PrefixTyped p' dps ->
  exists p'',
  PrefixConcat p p' p'' /\ (* from "such a p'' exists" *)
  PrefixTyped p'' s /\
  (forall dp'dps, Derivative p' dps dp'dps -> (* i.e. d_{p'}(d_p(s)) = `dp'dps` *)
    Derivative p'' s dp'dps).
Proof.
  intros.
  generalize dependent p'.
  generalize dependent dps.
  induction H0; intros.
  - sauto lq: on rew: off.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sinvert H.
    sinvert H1.
    + best.
    + edestruct IHPrefixTyped as [p00 [A [B C]]]; eauto.
      exists (PfxCatBoth p00 p2).
      split; try split.
     * hauto l: on.
     * sfirstorder use:pfx_cat_maximal.
     * sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sinvert H.
    sinvert H1.
    + sauto lq: on.
    + edestruct IHPrefixTyped as [p00 [A [B C]]]; eauto.
      exists (PfxStarRest p00 p2).
      split; try split.
      * hauto l: on.
      * sfirstorder use:pfx_cat_maximal.
      * sauto lq: on.
  - sauto lq: on.
Qed.
Hint Resolve pfx_cat_exists_when_typed : core.

(* TODO: prefix concatenation and derivatives,*)

Lemma pfx_cat_assoc : forall p q r s pq,
  PrefixConcat p q pq ->
  PrefixConcat pq r s ->
  exists qr, (PrefixConcat p qr s /\ PrefixConcat q r qr /\ (MaximalPrefix q -> q = qr)). (* had to strengthen this. *)
Proof.
  intros p q r s pq Hl Hr. generalize dependent r. generalize dependent s. induction Hl; intros. (* sauto lq: on. *)
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on rew: off.
  - sauto lq: on rew: off.
  - sinvert Hr. 
    edestruct (pfx_cat_maximal'' p'') as [U [V W]]; eauto.
    edestruct IHHl as [p0 [A [B C]]]; eauto.
    exists (PfxCatBoth p0 p'''0).
    split; try split.
    + constructor. assumption.
    + assert (p' = p0) by hauto lq: on rew: off use: pfx_cat_maximal'.
      destruct H.
      eapply PfxCatCatBoth.
      eauto.
      eapply pfx_cat_maximal'; eassumption.
    + intros. sinvert H.
      hauto lq: on rew: off use: pfx_cat_maximal'''.
  - sauto lq: on rew: off.
  - eexists; split; [| split]. 2: eassumption. { constructor. }
    intro. eapply pfx_cat_maximal'''; eassumption.
  - sauto lq: on rew: off use: pfx_cat_maximal'''.
  - sauto lq: on rew: off.
  - sfirstorder.
  - sauto lq: on rew: off use:pfx_cat_maximal'''.
  - sauto lq: on rew: off.
  - sinvert Hr. sauto lq: on rew: off use: pfx_cat_maximal', pfx_cat_maximal'''.
  - sinvert Hr. clear Hl H. specialize (IHHl _ _ H2) as [q [Hq1 [Hq2 Hq3]]]. eexists.
    split. { constructor; [| assumption]. eassumption. } split; assumption.
Qed.
Hint Resolve pfx_cat_assoc : core.

Lemma pfx_cat_assoc_eq : forall p q r pq qr s1 s2,
  PrefixConcat p q pq ->
  PrefixConcat q r qr ->
  PrefixConcat pq r s1 ->
  PrefixConcat p qr s2 ->
  s1 = s2.
Proof.
  intros p q r pq qr s1 s2 Hpq Hqr Hs1 Hs2.
  assert (A := pfx_cat_assoc _ _ _ _ _ Hpq Hs1). destruct A as [qr' [H1 [H2 _]]].
  assert (A := pfx_cat_unique _ _ _ _ Hqr H2). clear H2. symmetry in A. subst.
  assert (A := pfx_cat_unique _ _ _ _ Hs2 H1). subst. reflexivity.
Qed.
Hint Resolve pfx_cat_assoc_eq : core.

Theorem pfx_cat_typed : forall p p' p'' s dps,
  Derivative p s dps -> 
  PrefixTyped p s ->
  PrefixTyped p' dps ->
  PrefixConcat p p' p'' ->
  PrefixTyped p'' s.
Proof.
  intros.
  edestruct pfx_cat_exists_when_typed as [p''0 [V [W X]]]; eauto.
  destruct (ltac:(sfirstorder) : p'' = p''0).
  sfirstorder.
Qed.

Theorem pfx_cat_deriv : forall p p' p'' s dps,
  Derivative p s dps -> 
  PrefixTyped p s ->
  PrefixTyped p' dps ->
  PrefixConcat p p' p'' ->
  (forall dp'dps, Derivative p' dps dp'dps ->
    Derivative p'' s dp'dps).
Proof.
intros.
  edestruct (pfx_cat_exists_when_typed p p' s) as [p''0 [V [W X]]]; eauto.
  destruct (ltac:(sfirstorder) : p'' = p''0).
  sfirstorder.
Qed.

(*
Because we're using prop-valued sets not actual finite sets for sets of strings,
and functions not actual finite maps for environments, we cannot
prove that a concatenation exists. we must axiomatize a bunch of facts about this.
*)

Definition Subfunc (eta : env) eta' :=
  forall x p, eta x = Some p -> eta' x = Some p.

(* n'' is the greatest function defined some subset of dom(n) /\ dom(n') on which all concats exist -- and eta'' maps variables to those concats. *)
Definition EnvConcat : env -> env -> env -> Prop.
Admitted.

Axiom EnvConcat_char : forall eta eta' eta'',
  EnvConcat eta eta eta'' <-> (
    forall eta''',
        Subset (dom eta''') (dom eta) ->
        Subset (dom eta''') (dom eta') ->
        (forall x p p', dom eta''' x -> eta x = Some p -> eta' x = Some p' -> exists p'', PrefixConcat p p' p'' /\ eta''' x = Some p'') ->
        Subfunc eta''' eta''
  ).

(* by "greatest" *)
Theorem env_cat_unique : forall n n' n1 n2,
  EnvConcat n n' n1 -> 
  EnvConcat n n' n2 -> 
  n1 = n2.
Proof.
Admitted.

Theorem EnvConcat_lookup : forall eta eta' eta'' p'' x,
  EnvConcat eta eta' eta'' ->
  eta'' x = Some p'' ->
  exists p p', PrefixConcat p p' p'' /\ eta x = Some p /\ eta' x = Some p'.
Admitted.

(* defined on a subset of the intersection of the domains of eta and eta'. *)
Theorem EnvConcat_neither : forall eta eta' eta'' x,
  EnvConcat eta eta' eta'' ->
  eta x = None \/ eta' x = None ->
  eta'' x = None.
Proof.
Admitted.

(* if eta and eta' have concatenations on some subset of their intersection, then the envconcat exists, and that subset is a subset of the domain. *)
(* requires zorn's lemma *)
Theorem env_concat_exists : forall eta eta' s,
  Subset s (dom eta) ->
  Subset s (dom eta') ->
  (forall x p p', s x -> eta x = Some p -> eta' x = Some p' -> exists p'', PrefixConcat p p' p'') ->
  exists eta'', (EnvConcat eta eta' eta'' /\ (Subset s (dom eta''))).
Proof.
  (* eta'' = if eta(x) \/ eta'(x) null then null, else eta(x) . eta'(x)*)
Admitted.

Theorem env_cat_exists : forall eta eta' g g',
  WFContext g ->
  ContextDerivative eta g g' ->
  EnvTyped eta g ->
  EnvTyped eta' g' ->
  exists eta'', EnvConcat eta eta' eta'' /\ (Subset (fv g) (dom eta'')).
Proof.
  intros.
  assert (Subset (fv g) (dom eta)) by sfirstorder use:envtyped_dom.
  assert (Subset (fv g') (dom eta')) by sfirstorder use:envtyped_dom.
  assert (Subset (fv g) (dom eta')) by hauto lq: on use:fv_context_derivative.
  eapply (env_concat_exists eta eta' (fv g)); [eauto | eauto |].
  intros.
  clear H3.
  clear H4.
  clear H5.
  generalize dependent eta'.
  generalize dependent p.
  generalize dependent p'.
  dependent induction H0; intros.
  - sfirstorder.
  - sinvert H2. sinvert H3. hauto l: on use:pfx_cat_exists_when_typed.
  - sauto.
  - sauto.
Qed.

Theorem env_cat_maximal : forall s eta eta' eta'',
  EnvConcat eta eta' eta'' ->
  Subset s (dom eta'') ->
  MaximalOn s eta \/ MaximalOn s eta' -> MaximalOn s eta''.
Proof.
  intros.
  unfold MaximalOn in *. unfold PropOn in *. unfold PropOnItem in *.
  destruct H1; intros; edestruct subset_dom_lookup as [p'']; eauto; edestruct EnvConcat_lookup as [p [p' [U [V W]]]]; eauto; edestruct H1 as [p0 [A B]]; eauto.
  - destruct (ltac:(scongruence) : p = p0).
    exists p''.
    sfirstorder use:pfx_cat_maximal.
  - destruct (ltac:(scongruence) : p' = p0).
    exists p''.
    sfirstorder use:pfx_cat_maximal.
Qed.

Theorem env_cat_empty' : forall s eta eta' eta'',
  Subset s (dom eta'') ->
  EnvConcat eta eta' eta'' ->
  EmptyOn s eta ->
  EmptyOn s eta' ->
  EmptyOn s eta''.
Proof.
  unfold EmptyOn in *. unfold PropOn in *. unfold PropOnItem in *; intros; edestruct subset_dom_lookup as [p'']; eauto; edestruct EnvConcat_lookup as [p [p' [U [V W]]]]; eauto; edestruct H1 as [p0 [A B]]; eauto; exists p''; hauto l: on use:pfx_cat_empty.
Qed.

Theorem env_cat_typed : forall eta eta' eta'' g g',
  WFContext g ->
  ContextDerivative eta g g'->
  EnvTyped eta g ->
  EnvTyped eta' g' ->
  EnvConcat eta eta' eta'' ->
  Subset (fv g) (dom eta'')  ->
  EnvTyped eta'' g /\
  (forall g'', ContextDerivative eta' g' g'' ->
     ContextDerivative eta'' g g'').
Proof.
  intros.
  generalize dependent eta''.
  dependent induction H0; intros.
  - split. sfirstorder. sauto lq: on.
  - sinvert H. sinvert H2. sinvert H3.
    assert (H00 : exists p'', eta'' x = Some p'') by sfirstorder. edestruct H00 as [p''].
    edestruct EnvConcat_lookup as [p00 [p' [A [B C]]]]; eauto.
    destruct (ltac:(scongruence) : p = p0).
    destruct (ltac:(scongruence) : p = p00).
    destruct (ltac:(scongruence) : p1 = p').
    split.
    + econstructor. eauto. eapply pfx_cat_typed; eauto.
    + intros. sinvert H2. 
      destruct (ltac:(scongruence) : p0 = p1).
      econstructor. eauto. eapply pfx_cat_deriv; eauto.
  - econstructor; sauto lq: on.
  - sinvert H1. sinvert H2.
    assert (Subset (fv G) (dom eta'')) by sfirstorder.
    assert (Subset (fv D) (dom eta'')) by sfirstorder.
    split;[|sauto lq: on rew: off]. econstructor.
    + sauto lq: on.
    + sauto lq: on.
    + destruct H9; destruct H11.
      * left. eapply env_cat_empty'; eauto. { eapply prop_on_contains; [|eauto]. hauto l: on use:fv_context_derivative. }
      * right. eapply env_cat_maximal; eauto. { right. eapply prop_on_contains; [|eauto]. hauto l: on use:fv_context_derivative. }
      * right. eapply env_cat_maximal; eauto.
      * right. eapply env_cat_maximal; eauto.
Qed.


Theorem  env_cat_exists_when_typed : forall g g' eta eta',
  WFContext g ->
  ContextDerivative eta g g'->
  EnvTyped eta g ->
  EnvTyped eta' g' ->
  exists eta'',
  EnvConcat eta eta' eta'' /\
  Subset (fv g) (dom eta'') /\
  EnvTyped eta'' g /\
  (forall g'', ContextDerivative eta' g' g'' ->
     ContextDerivative eta'' g g'').
Proof.
  intros.
  edestruct env_cat_exists as [eta'' [A B]]; eauto.
  exists eta''.
  hauto l:on use:env_cat_typed.
Qed.
