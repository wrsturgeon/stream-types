Require Import Coq.Program.Equality.
From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Derivative
  Inert
  Nullable
  Prefix
  Subcontext
  Semantics
  History
  PrefixConcat
  SinkTerm
  Sets
  Terms
  Types
  RecSig
  Typing.

Definition Preserves i eta p s :=
    (MaximalOn s eta -> MaximalPrefix p) /\
    (i = Inert -> EmptyOn s eta -> EmptyPrefix p).
Arguments Preserves i eta p s/.

Theorem preserves_downgrade : forall i eta p s,
  Preserves i eta p s -> Preserves Jumpy eta p s.
Proof. split; intros; [| discriminate H0]. apply H. assumption. Qed.

Theorem preserves_to_agree : forall i eta p s S' S x,
Subset S' S ->
Preserves i eta p S' ->
Agree i eta (singleton_env x p) S (fv (CtxHasTy x s)).
Proof.
  intros.
  unfold Preserves in *.
  unfold Agree in *.
  destruct H0 as [A B].
  split; intros.
  + assert (MaximalOn S' eta) by sfirstorder use:prop_on_contains.
    cbn. intros. exists p. destruct H2. hauto lq: on use:eqb_refl.
  + assert (EmptyOn S' eta) by hauto l: on use:prop_on_contains.
    cbn. intros. exists p. destruct H3. hauto lq: on use:eqb_refl.
Qed.


Definition P_sound_inner (eta : env) (e : term) e' p g (rs :recsig) s (i : inertness) :=
  WFContext g ->
  EnvTyped eta g ->
    PrefixTyped p s /\
    (forall g' s', Derivative p s s' -> ContextDerivative eta g g' -> Typed nil g' NoRec e' s' Inert) /\
    Preserves i eta p (fv e).
Arguments P_sound_inner eta e e' p g rs s i/.

Definition P_sound eta e e' p :=
  forall g (rs : recsig) s (i : inertness),
  Typed nil g NoRec e s i ->
  P_sound_inner eta e e' p g rs s i.
Arguments P_sound eta e e' p/.

Definition P_sound_args eta_in g_out (args : argsterm) (args' : argsterm) g_out' eta_out :=
  forall g_in (i : inertness),
  ArgsTyped nil g_in NoRec args g_out i ->
  WFContext g_out ->
  WFContext g_in ->
  EnvTyped eta_in g_in ->
    EnvTyped eta_out g_out /\
    SetEq (dom eta_out) (fv g_out) /\
    (Agree i eta_in eta_out (fv args) (fv g_out)) /\
    (forall g_in', ContextDerivative eta_in g_in g_in' -> ArgsTyped nil g_in' NoRec args' g_out' Inert) /\
    ContextDerivative eta_out g_out g_out'.
Arguments P_sound_args eta_in g_out args args' g_out' eta_out/.


Theorem sound_sub : forall (G G' : context) (e : term) (s : type) eta e' p i,
  Step eta e e' p ->
  Subcontext G G' ->
  Typed nil G' NoRec e s i ->
  P_sound_inner eta e e' p G' NoRec s i ->
  P_sound_inner eta e e' p G NoRec s i.
Proof.
  unfold P_sound_inner. intros.
  edestruct H2 as [A [B C]]; [sfirstorder use: subtcontext_wf | sfirstorder use: sub_preserves_env |].
  repeat split.
  + sfirstorder.
  + intros.
    edestruct context_derivative_fun as [g'']. eapply sub_preserves_env; eauto.
    eapply TSubCtx. eapply subctx_deriv; eauto.
    hauto l:on.
  + sfirstorder.
  + sfirstorder.
Qed.

(* WILL: these preserves compat theorems! lets' work out the one for parl and catl2 *)
Theorem  preserves_cat_1 : forall (eta : env) e z p p' i x y t,
  x <> y ->
  eta z = Some (PfxCatFst p) ->
  Preserves i (env_union eta (env_union (singleton_env x p) (singleton_env y (emp t)))) p'  (fv e) ->
  Preserves i eta p' (fv (TmLetCat t x y z e)).
Proof.
intros.
destruct H1.
split.
- intros. 
  edestruct (H3 z) as [p0 [UU V]]. sfirstorder.
  destruct (ltac:(sfirstorder) : PfxCatFst p = p0).
  sinvert V.
- intros H00 H01. rewrite -> H00 in *.
  eapply H2; eauto.
  assert (H000 : EmptyOn (singleton_set z) eta) by hauto q: on.
  edestruct (H000 z) as [oop [LL MM]]; eauto. destruct (ltac:(scongruence) : PfxCatFst p = oop).
  assert (H00' : EmptyOn (set_minus (fv e) (set_union (singleton_set x) (singleton_set y))) eta) by best.
  sinvert MM.
  intro. intros.
  cbn in H00'.
  unfold PropOnItem in *.
  assert (H02 : x = x0 \/ y = x0 \/ (~(x = x0 \/ y = x0))) by admit.
  destruct H02 as [A | [B | C]].
  + rewrite <- A in *. exists p. hauto drew: off use:eqb_neq,eqb_eq.
  + rewrite <- B in *. exists (emp t). hauto q: on use:eqb_neq,eqb_eq,emp_empty.
  + edestruct (H00' x0) as [p0 [L M]]. sfirstorder.
    exists p0.
    cbn. hauto lq:on use:eqb_neq.
Admitted.

Theorem  preserves_cat_2 : forall (eta : env) e z p1 p2 p' i x y t,
  x <> y ->
  eta z = Some (PfxCatBoth p1 p2) ->
  Preserves i (env_union eta (env_union (singleton_env x p1) (singleton_env y p2))) p'  (fv e) ->
  Preserves i eta p' (fv (TmLetCat t x y z e)).
Proof.
Admitted.

Theorem  preserves_par : forall (eta : env) e z p1 p2 p' i x y,
  x <> y ->
  eta z = Some (PfxParPair p1 p2) ->
  Preserves i (env_union eta (env_union (singleton_env x p1) (singleton_env y p2))) p'  (fv e) ->
  Preserves i eta p' (fv (TmLetPar x y z e)).
Proof.
Admitted.


(* ArgsStep eta_in g_out e e' g_out' eta_out -> *)
(* P_sound_args g_in i e g_out eta_in e' g_out' eta_out. *)
Theorem sound_mut :
  (forall eta e e' p, Step eta e e' p -> P_sound eta e e' p) /\
  (forall eta_in g_out args args' g_out' eta_out,
    ArgsStep eta_in g_out args args' g_out' eta_out ->
    P_sound_args eta_in g_out args args' g_out' eta_out).
Proof.
  apply Step_mutual.
  1-23: (intros; intro G; intro rs; intro s00; intro i; intro Hty; dependent induction Hty; [|eapply sound_sub; try eassumption; hauto l: on]).
  all: intros; unfold P_sound_args in *; unfold P_sound in *; unfold P_sound_inner in *; intros.
  (* eps *)
  - sauto lq: on.
  (* one *)
  - sauto lq: on.
  (* var *)
  - split; try split.
      + hauto l: on use:maps_to_has_type_reflect.
      + intros. edestruct fill_derivative as [h [d' [A [B C]]]]; eauto.
        sinvert A.
        assert (p = p0) by scongruence.
        assert (s' = s'0) by sfirstorder use:derivative_det.
        sfirstorder.
      + qauto l: on.
  (* Par-R *)
  - admit.
    (* edestruct H as [A [B [C L]]]; eauto.
    edestruct H0 as [A' [B' [C' L']]]; eauto.
    split; try split; try split.
    + sauto lq: on.
    + intros. sinvert H4. econstructor; eauto. sfirstorder.
    + sfirstorder.
    + intros. rewrite -> H4 in *. edestruct i_ub_inert as [H00 H01]; eauto. rewrite H00 in *. rewrite H01 in *. sfirstorder. *)
  (* Cat-R-1 *)
  - admit.
    (* edestruct H as [A [B [C L]]]; eauto.
    sinvert H1.
    sinvert H2.
    destruct H10;[|shelve].
    split; try split; try split.
    + sauto lq: on.
    + intros. sinvert H2. sinvert H3. assert (H00 : D = D') by best use:context_derivative_emp'. rewrite -> H00 in *. econstructor. eauto. eauto. assert (~(Nullable s'0)). { intro. assert (MaximalPrefix p).  eapply maximal_derivative_nullable'; eauto. sfirstorder. } sfirstorder.
    + intros. sfirstorder.
    + intros. sfirstorder.
    Unshelve.
    assert (MaximalOn (fv e1) n). { eapply prop_on_contains. eapply typing_fv. eauto. eauto. }
    assert (MaximalPrefix p) by sauto lq: on.
    best. *)
  (* Cat-R-2 *)
  - admit.
    (* edestruct H as [A [B C]]; eauto.
    edestruct H0 as [A' [B' C']]; eauto.
    split; try split; try split.
    + hauto l: on.
    + intros. sinvert H5. sinvert H4. eapply TSubCtx; [|eauto]. hauto l: on.
    + intros. sfirstorder.
    + intros H00 H01. rewrite -> H00 in *. unfold inert_guard in *.
      sinvert H2. sinvert H3.
      edestruct H1 as [UU UU']; eauto; eauto.
      rewrite -> UU in *.
      assert (EmptyOn (fv e1) n) by hauto q: on use:prop_on_contains.
      assert (EmptyPrefix p1) by best.
      assert (Nullable s1) by best use:empty_and_maximal_means_nullable.
      best. *)
  (* Par-L *)
  - 
    assert (H00 : PrefixTyped (PfxParPair p1 p2) (TyPar s0 t)) by hauto l: on use: maps_to_has_type_reflect.
    sinvert H00. edestruct H as [A [B C]].
    + sfirstorder.
    + eassumption.
    + eapply wf_fill_reflect; eauto; repeat split. hauto l: on. sauto. hauto q: on. sfirstorder.
    + eapply parlenvtyped; eauto.
    + repeat split.
      * sfirstorder.
      * intros. edestruct fill_derivative as [G' [zst' [A' [B' [C' D']]]]];
        [| eassumption |]; [eassumption |]. sinvert A'. sinvert H18.
        assert (p0 = p1) by congruence. assert (p3 = p2) by congruence. subst.
        specialize (D' (CtxComma (CtxHasTy x s0) (CtxHasTy y t))).
        specialize (D' (CtxComma (CtxHasTy x s'1) (CtxHasTy y t'))).
        specialize (D' Gxsyt (env_union (singleton_env x p1) (singleton_env y p2))).
        edestruct D' as [u [A'' B'']]; [eassumption | | |].
        -- eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. intros. assert (H00 : (dom (singleton_env x p1) x0) \/ (dom (singleton_env y p2) x0)) by hauto l:on use:dom_singleton',dom_union'; destruct H00; hauto l:on use:dom_singleton'.
        -- eapply context_derivative_comma; try (eapply context_derivative_sng; eassumption).
           intro test. cbn. destruct (eqb_spec x test); destruct (eqb_spec y test); sfirstorder.
        -- econstructor; [eauto | eauto | eauto | | | eauto | eauto |]. hauto q:on drew:off use:fv_hole_derivative. hauto q:on drew:off use:fv_hole_derivative. eapply B; eauto.
      * intros. eapply C. admit.
      * intros H00 H01. admit.
  (* cat-l-1 *)
  - assert (H00 : PrefixTyped (PfxCatFst p) (TyDot s0 t)) by best use:maps_to_has_type_reflect.
    sinvert H00. edestruct H as [A [B C]]. eauto. eauto. eauto. eapply catrenvtyped1; eauto.
    assert (DisjointSets (dom (singleton_env x p)) (dom (singleton_env y (emp t)))). { eapply DisjointSets_inj. intros x0 H00. intro H01. eapply dom_singleton in H00. eapply dom_singleton in H01. scongruence. }
    assert (DisjointSets (dom (env_union (singleton_env x p) (singleton_env y (emp t)))) (fv G)). { eapply DisjointSets_inj. intros x0 H00. intro H01. eapply dom_union in H00. destruct H00; eapply dom_singleton in H12; scongruence. }
    split; try split.
    + sfirstorder.
    + intros. edestruct (fill_derivative n) as [G' [dzst [A' [B' [C' D']]]]];[|eauto|]. eauto.
      sinvert A'. 
      destruct (ltac:(scongruence) : PfxCatFst p = p0).
      sinvert H21.
      edestruct (D' (CtxSemic (CtxHasTy x s0) (CtxHasTy y t)) (CtxSemic (CtxHasTy x s'1) (CtxHasTy y t)) Gxsyt (env_union (singleton_env x p) (singleton_env y (emp t)))) as [G'xs'1yt [U V]]. eauto. { eapply no_conflict_on_disjoint. hauto l: on. } { eapply context_derivative_semic; [eauto| |]; eapply context_derivative_sng. eauto. hauto l:on use:derivative_emp. }
      econstructor; [ eauto | eauto | eauto | eauto | eauto | | | eauto | | ]. best use:step_bv. best use:step_bv. hauto q: on use:fv_hole_derivative. hauto q: on use:fv_hole_derivative. eauto.
      hauto l: on.
    + eapply preserves_cat_1; eauto.
  (* cat-l-2 *)
  - assert (H00 : PrefixTyped (PfxCatBoth p1 p2) (TyDot s0 t)) by best use:maps_to_has_type_reflect.
    sinvert H00. edestruct H as [A [B C]]. eauto. eauto. eauto. eapply catrenvtyped2; eauto.
    split; try split.
    + sfirstorder.
    + intros. edestruct fill_derivative as [G' [zst' [A' [B' [C' D']]]]]; eauto.
      sinvert A'.
      destruct (ltac:(scongruence) : (PfxCatBoth p1 p2) = p).
      sinvert H21.
      edestruct (derivative_fun p1 s0) as [s'']; eauto.
      assert (DisjointSets (dom (singleton_env x p1)) (dom (singleton_env y p2))). { eapply DisjointSets_inj. intros x0 H00. intro H01. eapply dom_singleton in H00. eapply dom_singleton in H01. scongruence. }
      specialize (D' (CtxSemic (CtxHasTy x s0) (CtxHasTy y t)) (CtxSemic (CtxHasTy x s'') (CtxHasTy y s'0)) Gxsyt (env_union (singleton_env x p1) (singleton_env y p2))).
      edestruct D' as [u [A'' B'']]. eauto. { eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. intros x0 H00. eapply dom_union in H00. destruct H00; eapply dom_singleton in H18; scongruence. } eapply context_derivative_semic; [eauto | | ]; eapply context_derivative_sng; eauto.
      specialize (B u s').
      edestruct (fill_reflect_fun G' (CtxSemic CtxEmpty (CtxHasTy z s'0))) as [g''].
      eapply (TSubCtx g' g''); [ eapply (SubCong G'); eauto |].
      remember (hole_compose G' (HoleSemicL HoleHere (CtxHasTy z s'0))).
      assert (DisjointSets (fv G) (singleton_set z)). { edestruct (wf_fill_reflect G); eauto. hauto l: on. }
      assert (HoleCompose G' (HoleSemicL HoleHere (CtxHasTy z s'0)) h) by best use:reflect_hole_compose.
      eapply (TLet h CtxEmpty (fill G' (CtxSemic (CtxHasTy x s'') (CtxHasTy z s'0)))).
        { intro H00. eapply hole_compose_fv in H00;[|eauto]. edestruct H00. hauto q:on use:fv_hole_derivative. sfirstorder. }
        sfirstorder.
        sfirstorder use:sink_tm_typing.
        { eapply hole_compose_fill. eauto. exists (CtxSemic (CtxHasTy x s'') (CtxHasTy z s'0)). split. hauto l:on. hauto l: on use:reflect_fill. }
        { eapply hole_compose_fill. eapply reflect_hole_compose; eauto. exists (CtxSemic CtxEmpty (CtxHasTy z s'0)). split. hauto l:on. scongruence use:reflect_fill. }
        eapply typing_subst'. eauto. { admit. (* true *) } { admit. (*true*) } { intro H00. eapply step_bv in H00;[|eauto]. best. } { intro H00. eapply step_bv in H00;[|eauto]. scongruence. } { admit. (* true!*) }
    + eapply preserves_cat_2; eauto.
  (* Let *)
  - 
    edestruct H as [A [B [U V]]]; eauto.
   (* todo: need better automation for disjoitnness *)
    assert (NoConflictOn eta (singleton_env x p) (fv G)). { eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. intros. intro. assert (x0 <> x) by scongruence. assert (x = x0) by qauto l: on use:dom_singleton. sfirstorder. }
    assert (EnvTyped (env_subst x p eta) Gxs). eapply env_subctx_bind'; [ | eauto | eauto | | | ]. eauto. eauto. { eapply env_typed_singleton. eauto. } { eapply preserves_to_agree. eapply typing_fv; eauto. sfirstorder. }
    edestruct (wf_fill_reflect G) as [QQ _]; eauto.
    assert (WFContext Gxs). { eapply wf_fill_reflect. eauto. best use:DisjointSets_inj'. }
    edestruct H0 as [A' [B' [U' V']]]; eauto.
    split; try split; try split.
    + eauto.
    + intros GD' t'. intros.
      edestruct (fill_derivative eta G D GD GD') as [G' [D' [L [M [N O]]]]]; eauto.
      edestruct (derivative_fun p) as [s']; eauto.
      assert (Typed nil D' NoRec e1' s' Inert) by hauto l: on.
      edestruct (O (CtxHasTy x s1) (CtxHasTy x s') Gxs (singleton_env x p)) as [G'xs' [W X]]. eauto. eauto. hauto l: on.
      econstructor; [ | | eauto | | eauto | ]. hauto q:on use:fv_hole_derivative. hauto q:on use:fv_context_derivative. eauto.
      eapply B'; eauto. 
    + intros. assert (MaximalOn (set_minus (fv e2) (singleton_set x)) eta) by hauto q: on.
      eapply U'. eapply prop_on_minus. eapply U. hauto q: on. eauto.
    + intros. assert (EmptyOn (set_minus (fv e2) (singleton_set x)) eta) by hauto q: on.
      eapply V'. eauto. eapply prop_on_minus. eapply V. eauto. hauto q: on. eauto.
  (* inl *)
  - sauto lq: on.
  (* inr *)
  - sauto lq: on.
  (* sum-l-1 *)
  -
    split; try split; try split.
    + best use:emp_well_typed.
    + intros.
      assert (Derivative (emp r) r r) by best use:derivative_emp.
      destruct (ltac:(sfirstorder use:derivative_det) : r = s').
      edestruct (env_cat_exists_when_typed Gz) as [eta''0 [A [B [C D]]]]; eauto.
      destruct (ltac:(hauto l:on use:env_cat_unique) : eta'' = eta''0).
      eapply TPlusCase; eauto. 
    + assert (Subset (singleton_set z) (fv (TmPlusCase eta' r z x e1 y e2))) by sfirstorder.
      intro HM. eapply (prop_on_contains) in HM; [|eauto].
      assert (MaximalOn (singleton_set z) eta''). { eapply env_cat_maximal. eauto. qauto l: on. hauto l:on. }
      assert (Hcontra : MaximalPrefix PfxSumEmp) by qauto l:on.
      sinvert Hcontra.
    + best use:emp_empty.
  (* sum-l-2 *)
  - 
    assert (WFContext Gz) by sfirstorder use:context_derivative_wf'.
    assert (Hwf : WFHole G /\ DisjointSets (fv G) (singleton_set z)) by sauto use:wf_fill_reflect.
    destruct Hwf.
    assert (~ fv G z) by sfirstorder.
    assert (WFHole G). { eapply (wf_fill_reflect G (CtxHasTy z _)). eauto. sfirstorder use:context_derivative_wf'. }
    edestruct (env_cat_exists_when_typed Gz) as [eta''0 [A [B [C D]]]]; eauto.
    destruct (ltac:(sfirstorder use:env_cat_unique) : eta'' = eta''0).
    assert (Hty : exists p0, eta'' z = Some p0 /\ PrefixTyped p0 (TySum s0 t)) by best use:maps_to_has_type_reflect.
    edestruct Hty as [p0 [L M]].
    destruct (ltac:(scongruence) : PfxSumInl p = p0).
    sinvert M.
    edestruct H as [A' [B' [C' D']]]. eauto. eauto. { eapply wf_fill_reflect. eauto. sfirstorder. } { eapply sumcaseenvtyped1; eauto. }
    split; try split; try split.
    + eauto.
    + intros.
      edestruct (fill_derivative eta'' G (CtxHasTy z (TySum s0 t))) as [G' [d_s [A'' [B'' [C'' D'']]]]]; [eauto | eapply D; eauto |]. 
      sinvert A''.
      destruct (ltac:(scongruence) : PfxSumInl p = p0).
      sinvert H27.
      assert (WFContext Gx). { eapply wf_fill_reflect. eauto. hauto drew: off. }
      edestruct (D'' (CtxHasTy x s0) (CtxHasTy x s'0) Gx (singleton_env x p)) as [Gx' [U V]]. eauto. { eapply no_conflict_on_disjoint. right. eapply wf_fill_reflect in H22;[|eauto]. eapply DisjointSets_inj. intros. destruct H22 as [_ [_ U]]. eapply U. eapply dom_singleton in H23. scongruence. } eapply context_derivative_sng; eauto.
      eapply (typing_subst'). eauto. hauto l:on use:context_derivative_wf. { intro. eapply fv_fill in H23;[|eauto]. destruct H23; [scongruence|]. assert (DisjointSets (fv G) (singleton_set z)) by best use:wf_fill. assert (H00 : ~fv G z) by scongruence. eapply H00. hauto drew: off use:fv_hole_derivative. } { intro. eapply H3. eapply step_bv;eauto. } { best. } { eapply ctx_subst_fill; eauto. }
    + intros.
      assert (MaximalOn (set_union (set_minus (fv e1) (singleton_set x)) (singleton_set z)) eta) by hfcrush use:prop_on_contains.
      assert (MaximalOn (set_union (set_minus (fv e1) (singleton_set x)) (singleton_set z)) eta''). eapply env_cat_maximal; [ eauto | | ].
      { intro x0. intro H00. destruct H00; [|hauto drew: off]. edestruct H22. eapply B. eapply fv_fill. eauto. right. eapply fv_fill' in H6. eapply typing_fv in H23; [|eauto]. hauto q:on use:fv_fill. }
      hauto lq: on rew: off.
      edestruct (H22 z) as [p00 [L' R]]. hauto lq: on rew: off.
      destruct (ltac:(scongruence) : PfxSumInl p = p00).
      sinvert R.
      eapply C'. eapply prop_on_minus. eauto. qauto l: on.
    + intros H00 H01.
      rewrite -> H00 in *.
      assert (eta' z = Some PfxSumEmp) by sfirstorder.
      assert (EmptyOn (singleton_set z) eta) by hauto q: on use:prop_on_contains.
      assert (EmptyOn (singleton_set z) eta') by sblast.
      assert (H02 : EmptyOn (singleton_set z) eta''). eapply env_cat_empty'; [ | eauto | eauto | eauto]. scrush.
      edestruct (H02 z) as [p'' [UU UU']]; eauto.
      destruct (ltac:(scongruence) : PfxSumInl p = p'').
      sinvert UU'.
  (* sum-l-3 *)
  - admit.

  (* nil *)
  - sauto lq: on.
  (* cons-1 *)
  - edestruct H as [A [B [C L]]]; eauto.
    sinvert H1; sinvert H0.
    destruct H7;[|shelve].
    repeat split.
    + sauto lq: on.
    + intros. sinvert H1; sinvert H2. assert (H00 : D = D') by best use:context_derivative_emp'. rewrite -> H00 in *. econstructor. eauto. eauto. assert (~(Nullable s'0)). { intro. assert (MaximalPrefix p).  eapply maximal_derivative_nullable'; eauto. sfirstorder. } sfirstorder.
    + intros. sfirstorder.
    + scongruence.
    Unshelve.
    assert (MaximalOn (fv e1) n). { eapply prop_on_contains. eapply typing_fv. eauto. eauto. }
    assert (MaximalPrefix p) by sauto lq: on.
    scongruence.
  (* cons-2*)
  - edestruct H as [A [B C]]; eauto.
    edestruct H0 as [A' [B' C']]; eauto.
    repeat split.
    + hauto l: on.
    + intros. sinvert H3. sinvert H4. eapply TSubCtx; [|eauto]. hauto l: on.
    + intros. sfirstorder.
    + scongruence.
  (* fix *)
  - edestruct H as [A [B [[U V] [D E]]]]; eauto.
    assert (Typed nil g NoRec (histval_subst_all vs (fix_subst g r e e)) r i). eapply typing_histval_subst_all. { eapply typing_fix_subst; eauto. } { eapply HistArgsStep_sound; eauto. }
    edestruct H0 as [A' [B' [C' D']]]; eauto.
    split; try split; try split.
    + eauto.
    + intros. econstructor; [ hauto l:on use:context_derivative_wf|hauto l:on|hauto l: on].
    + intros. eapply C'. eapply (prop_on_contains MaximalPrefix (fv g)); hauto l: on use:typing_fv.
    + intros H00 H01. rewrite -> H00 in *. eapply D'; eauto. eapply (prop_on_contains EmptyPrefix (fv g)); hauto l: on use:typing_fv.
  (* argscut *)
  - edestruct H as [A [B [[U V] [D E]]]]; eauto.
    assert (WFContext g') by hauto l:on use:context_derivative_wf.
    edestruct H0 as [A' [B' [C' D']]]; eauto.
    split; try split; try split.
    + sfirstorder.
    + hauto l: on.
    + intros. eapply C'. eapply (prop_on_contains MaximalPrefix (fv g)). hauto l:on use:typing_fv. eapply U. sfirstorder.
    + intros H00 H01. rewrite -> H00 in *. eapply D'. eauto. assert (Subset (fv e) (fv g)) by hauto l:on use:typing_fv. eapply prop_on_contains. eauto. eapply V. eauto. sfirstorder.
  - edestruct histval_lift_fun as [p' [A [B C]]]; eauto. eapply HistStep_sound; eauto.
    destruct (ltac:(sfirstorder use:histval_lift_det) : p = p').
    repeat split; hauto l: on use:sink_tm_typing.
  (* wait 1 *)
  - repeat split.
    + sfirstorder use:emp_well_typed.
    + intros. destruct (ltac:(sfirstorder use: derivative_emp') : r = s').
      edestruct (env_cat_exists_when_typed Gx) as [eta''0 [A [B [C D]]]]; [ sfirstorder use:context_derivative_wf' |eauto|eauto|eauto|eauto]. 
      destruct (ltac:(sfirstorder use:env_cat_unique) : eta'' = eta''0).
      econstructor; eauto. { cbn. intros. split; [scongruence|]. intro. assert (H00 : PrefixTyped p s) by hauto l: on use:maps_to_has_type_reflect. eapply nullable_means_maximal in H00;[|eauto]. sfirstorder. }
    + intros.
      edestruct (EnvConcat_lookup z) as [p0 [p1 [A' [B' C']]]]. eauto. eauto.
      assert (MaximalPrefix p1) by best.
      hauto lq: on use:pfx_cat_maximal.
    + sfirstorder use:emp_empty.
  (* wait 2 *)
  - edestruct (env_cat_exists_when_typed Gx) as [eta''0 [A [B [C D]]]]; [ sfirstorder use:context_derivative_wf' |eauto|eauto|eauto|eauto]. 
    destruct (ltac:(sfirstorder use:env_cat_unique) : eta'' = eta''0).
    assert (PrefixTyped p s) by hauto l:on use:maps_to_has_type_reflect.
    assert (WFContext Gemp). { eapply wf_fill_reflect;[eauto|]. repeat split; [ | eauto|eauto|eauto]. eapply context_derivative_wf' in H5;[ | eauto]. sfirstorder use:wf_fill_reflect. }
    assert (EnvTyped eta'' Gemp). { eapply (fill_preserves_env (CtxHasTy z s)). eauto. eauto. hauto l: on. sfirstorder. eauto. }
    edestruct H as [A' [B' C']]; [eauto | | eauto | eauto | ]. { assert (H00 : app (nil : list histty) nil = nil) by scongruence. rewrite <- H00. eapply typing_histval_subst. eauto. sfirstorder. sfirstorder. eapply maximal_prefix_flatten'; eauto. } 
    assert (H00 : SetEq (fv (histval_subst v 0 e)) (fv e)) by best use:fv_histval_subst.
    repeat split.
    + eauto.
    + intros. 
      assert (ContextDerivative eta'' Gx g'). eapply D; eauto.
      edestruct (fill_derivative eta'') as [G'' [d_d [U [V [W X]]]]]; [|eauto|]; eauto.
      sinvert U.
      destruct (ltac:(scongruence) : p = p1).
      edestruct (X CtxEmpty CtxEmpty Gemp eta'') as [G''emp [L M]]; [eauto|scongruence|sfirstorder|]. 
      eapply (TSubCtx g' G''emp); [eapply SubCong; eauto|]; eapply B'; [eauto| scongruence use:env_union_idemp].
    + intros.
      assert (MaximalOn (fv e) eta) by hauto q: on use:prop_on_contains.
      eapply C'. eapply (prop_on_contains MaximalPrefix (fv e)); [hauto q: on|].
      eapply env_cat_maximal; [eauto| |eauto]. { intro x0; intro H01; eapply B; eapply fv_fill; [eauto|]; right. eapply typing_fv in H01;[|eauto]. hauto q:on use:fv_fill. }
    + intros. rewrite -> H10 in *.
      edestruct H3; eauto.
      assert (H01 : EmptyOn (singleton_set z) eta) by hauto q: on use:prop_on_contains.
      edestruct (H01 z) as [p1 [U V]]; eauto.
      edestruct (EnvConcat_lookup z) as [p0' [p1' [L [M N]]]]; eauto.
      edestruct (ltac:(scongruence) : p1 = p1').
      edestruct (maps_to_has_type_reflect eta') as [p0'' [UU VV]]; [|eauto|]; eauto.
      destruct (ltac:(scongruence) : p0' = p0'').
      edestruct (fill_derivative eta' G (CtxHasTy z s)) as [G' [d_d [L' [M' [N' O']]]]]; eauto.
      sinvert L'.
      destruct (ltac:(scongruence) : p0' = p2).
      assert (~ MaximalPrefix p0') by sfirstorder.
      assert (H02 : ~ Nullable s') by hauto l:on use:maximal_derivative_nullable'.
      assert (MaximalPrefix p1) by hauto l: on use:pfx_cat_maximal'.
      assert (~ MaximalPrefix p). {
        intro.
        eapply H02.
        eapply empty_and_maximal_means_nullable; eauto. hauto l: on use:maps_to_has_type_reflect.
      }
      scongruence.
  (*** args ****)
  - best.
  - sinvert H0.
     edestruct H as [A [B C]]; eauto.
    split; try split; try split; try split.
    + eapply env_typed_singleton; eauto.
    + sfirstorder use:dom_singleton.
    + sfirstorder use:dom_singleton.
    + eapply preserves_to_agree; [| hauto lq: on rew: off ]. hauto l: on use:typing_fv.
    + eapply preserves_to_agree; [| hauto lq: on rew: off ]. hauto l: on use:typing_fv.
    + intros. hauto l: on.
    + hauto l: on.
  - sinvert H1. sinvert H2.
    edestruct H as [A [B [C [D E]]]]; eauto.
    edestruct H0 as [F [G [L [I J]]]]; eauto.
    assert (H00 : fv (CtxComma g1 g2) = set_union (fv g1) (fv g2)) by scongruence; rewrite -> H00 in *.
    split; try split; try split; try split.
    + eapply env_typed_comma; [| eauto | eauto]. hauto q: on.
    + hauto q: on.
    + hauto drew: off.
    + intros.  eapply prop_on_set_union. split.
      * eapply prop_on_weakening_alt'. eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. qauto l: on use:empty_env_for_dom.
        hauto q: on.
      * eapply prop_on_weakening. sfirstorder.
    + intros. edestruct i; try scongruence. assert (H00' : i1 = Inert /\ i2 = Inert) by hauto l:on use:i_ub_inert; destruct H00' as [UU UU']; rewrite -> UU in *; rewrite -> UU' in *.
      eapply prop_on_set_union; split.
      * eapply prop_on_weakening_alt'; [| sfirstorder]. { eapply no_conflict_on_disjoint. right. eapply (DisjointSets_eq string (fv g2) (fv g1)); [eauto | |]; sfirstorder. }
      * eapply prop_on_weakening. sfirstorder.
    + intros; econstructor; eauto. sfirstorder.
    + eapply context_derivative_comma; [| eauto | eauto]. hauto q: on.
  - sinvert H0; sinvert H1; sinvert H2; sinvert H3.
    edestruct H as [A [B [C [D E]]]]; eauto.
    split; try split; try split; try split.
    + eapply env_typed_semic; [| eauto| sfirstorder use:empty_env_for_typed | hauto lq: on use:empty_env_for_empty_on] . 
      (* clear D; clear C; clear H13; clear H9; clear H11; clear H; clear H0; clear IHArgsStep. *)
      assert (Subset (fv g1) (dom eta1)) by best use:envtyped_dom.
      assert (Subset (fv g0) (dom eta)) by best use:envtyped_dom.
      hauto lq:on rew: off use:empty_env_for_dom.
    + cbn. hauto q: on use:empty_env_for_dom.
    + cbn. hauto q: on use:empty_env_for_dom.
    + intros. sfirstorder.
    + intros H00 H01. rewrite -> H00 in *.
      unfold inert_guard in *. assert (H02 : i1 = Inert) by best. rewrite -> H02 in *.
      assert (H03 : fv (CtxSemic g1 g2) = set_union (fv g1) (fv g2)) by best. rewrite -> H03 in *. eapply prop_on_set_union. split.
      * eapply prop_on_weakening_alt'. eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. qauto l: on use:empty_env_for_dom.
        hauto q: on.
      * eapply prop_on_weakening. hauto q: on use:empty_env_for_empty_on.
    + intros. sinvert H0.
      destruct H15.
      *  assert (H00 : D' = g3) by best use:context_derivative_emp'.
         rewrite <- H00 in *.
         econstructor; eauto.
         assert (~(MaximalOn (fv e1) eta)) by best.
         unfold inert_guard in *.
         intros. split; try split. auto.
         intro.
         assert (MaximalOn (fv g0) eta) by sfirstorder use: maximal_context_derivative_nullable'.
         assert (MaximalOn (fv e1) eta) by best use:typing_fv_args.
         scongruence.
      (* contradictory. *)
      * assert (MaximalOn (fv g1) eta1). { eapply C. eapply prop_on_contains; [|eauto]. hauto l:on use:typing_fv_args. } sfirstorder.
    + eapply context_derivative_semic. { eapply (DisjointSets_eq string (fv g1) (fv g2)). eauto. qauto l:on use:empty_env_for_dom. eauto. } eauto. hauto l: on use:context_derivative_emp.
  - sinvert H1; sinvert H2; sinvert H3; sinvert H4.
    edestruct H as [A [B [C [D DU]]]]; eauto.
    edestruct H0 as [E [F [G [H' H'U]]]]; eauto.
    split; try split; try split; try split.
    + eapply env_typed_semic; [| eauto | eauto | eauto]. hauto q: on.
    + hauto q: on.
    + hauto drew: off.
    + intros. 
      assert (H03 : fv (CtxSemic g1 g2) = set_union (fv g1) (fv g2)) by scongruence. rewrite -> H03 in *. 
      eapply prop_on_set_union.
      split.
      * eapply prop_on_weakening_alt';[|eauto]; eapply no_conflict_on_disjoint. right. { eapply (DisjointSets_eq string (fv g2) (fv g1)); [eauto | | ]; sfirstorder. }
      * sfirstorder use: prop_on_weakening.
    + intros H00 H01; rewrite -> H00 in *. unfold inert_guard in *. assert (H02 : i1 = Inert) by sfirstorder. rewrite -> H02 in *.
      (* if eta were empty, this shouldn't happen. because *)
      edestruct H15; eauto.
      assert (H03 : fv (CtxSemic g1 g2) = set_union (fv g1) (fv g2)) by scongruence. rewrite -> H03 in *. 
      (* assert (H04 : fv (CtxSemic g0 g3) = set_union (fv g0) (fv g3)) by scongruence. *)
      assert (EmptyOn (fv e1) eta) by hauto l:on use:prop_on_set_union.
      assert (EmptyOn (fv g1) eta1) by sauto lq: on.
      assert (NullableCtx g1) by hauto l: on use:emptyon_and_maximalon_means_nullable.
      scongruence. (* contradiction: g1 is and isn't nullable. *)
    + intros. sinvert H1. econstructor; [|eauto]. eapply maximal_context_derivative_nullable; eauto.
    + eapply context_derivative_semic; [|eauto|eauto]. { eapply (DisjointSets_eq string (fv g1) (fv g2)); eauto. }
  - sinvert H0. sinvert H1. sinvert H2. sinvert H3.
    edestruct H as [A [B [C [D E]]]]; eauto.
    assert (H03 : fv (CtxSemic g1 g2) = set_union (fv g1) (fv g2)) by scongruence. rewrite -> H03 in *. 
    split; try split; try split; try split.
    + eapply env_typed_semic. { eapply (DisjointSets_eq string (fv g1) (fv g2)); [| eauto | eauto]; hauto lq: on use:empty_env_for_dom. } hauto l:on use:empty_env_for_typed. eauto. { right.  eapply nullable_context_means_maximalon. eauto. hauto l:on use:empty_env_for_typed. }
    + hauto q: on use:empty_env_for_dom.
    + hauto drew: off use:empty_env_for_dom.
    + intros. eapply prop_on_set_union; split.
      * eapply prop_on_weakening_alt'. { eapply no_conflict_on_disjoint. right. eapply (DisjointSets_eq string (fv g2) (fv g1)); [| | eauto]; sfirstorder. } {eapply nullable_context_means_maximalon. eauto. hauto l:on use:empty_env_for_typed. }
      * eapply prop_on_weakening; sfirstorder.
    + intros H00 H01. rewrite  -> H00 in *.
      eapply prop_on_set_union; split.
      * eapply prop_on_weakening_alt'; [| hauto q: on use:empty_env_for_empty_on]. { eapply no_conflict_on_disjoint. right. eapply (DisjointSets_eq string (fv g2) (fv g1)); [| | eauto]; sfirstorder. }
      * eapply prop_on_weakening; hauto l: on.
    + intros. sinvert H0. econstructor; eauto.
    + eapply context_derivative_semic. { eapply (DisjointSets_eq string (fv g1) (fv g2)); [| eauto | eauto]; hauto lq: on use:empty_env_for_dom. } hauto l: on use:context_derivative_emp. eauto.
Admitted.
