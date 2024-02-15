Require Import Coq.Program.Equality.
From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Derivative
  Ind
  Inert
  Nullable
  Prefix
  Subcontext
  Semantics
  PrefixConcat
  SinkTerm
  Sets
  Terms
  Types
  RecSig
  Typing.

(* Theorem agree_step_inert : forall e e' eta p S x s,
  Inert e ->
  Subset (fv e) S -> (*automatic from typing derivatino*)
  Step eta e e' p ->
  PrefixTyped p s ->
  Agree Inert eta (singleton_env x p) S (singleton_set x)
.
Proof.
  intros.
  unfold Agree. split; intros.
  - assert (MaximalOn (fv e) eta); [eapply prop_on_contains; eauto |].
    assert (MaximalPrefix p) by sfirstorder use:maximal_push.
    exists p. sinvert H6. unfold singleton_env. hauto lq: on use:eqb_refl. 
  - assert (EmptyOn (fv e) eta); [eapply prop_on_contains; eauto |].
    assert (EmptyPrefix p) by hauto lb: on drew: off use:empty_push_inert.
    exists p. sinvert H6. unfold singleton_env. hauto lq: on use:eqb_refl.
Qed. *)

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

Definition P_sound g (rs : recsig) (e : term) s (i : inertness) eta (e' : term) p :=
  Typed g NoRec e s i ->
  WFContext g ->
  EnvTyped eta g ->
    PrefixTyped p s /\
    (forall g' s', Derivative p s s' -> ContextDerivative eta g g' -> Typed g' NoRec e' s' Inert) /\
    Preserves i eta p (fv e).
Arguments P_sound g rs e s i eta e' p/.

Definition P_sound_args g_in (i : inertness) (e : argsterm) g_out eta_in (e' : argsterm) g_out' eta_out :=
  ArgsTyped g_in NoRec e g_out i ->
  WFContext g_out ->
  WFContext g_in ->
  EnvTyped eta_in g_in ->
    EnvTyped eta_out g_out /\
    SetEq (dom eta_out) (fv g_out) /\
    (Agree i eta_in eta_out (fv g_in) (fv g_out)) /\
    (forall g_in', ContextDerivative eta_in g_in g_in' -> ArgsTyped g_in' NoRec e' g_out' Inert).
Arguments P_sound_args g_in i e g_out eta_in e' g_out' eta_out/.

Theorem sound_sub : forall (G G' : context) (e : term) (s : type) eta e' p i,
  Step eta e e' p ->
  Subcontext G G' ->
  Typed G' NoRec e s i ->
  P_sound G' NoRec e s i eta e' p ->
  P_sound G NoRec e s i eta e' p.
Proof.
  unfold P_sound. intros.
  edestruct H2 as [A [B C]]; [eauto | sfirstorder use: subtcontext_wf | sfirstorder use: sub_preserves_env |].
  repeat split.
  + sfirstorder.
  + intros.
    edestruct context_derivative_fun as [g'']. eapply sub_preserves_env; eauto.
    eapply TSubCtx. eapply subctx_deriv; eauto.
    hauto l:on.
  + sfirstorder.
  + sfirstorder.
Qed.


Theorem sound : forall G e s i eta e' p,
  Step eta e e' p ->
  P_sound G NoRec e s i eta e' p.
Proof.
  intros. generalize dependent G. generalize dependent s. generalize dependent i.
  induction H; intros i s G Ht; intros;
  (dependent induction Ht; [| eapply sound_sub; try eassumption; hauto l: on]).
  - admit.
  - admit.
  - split; try split.
      + hauto l: on use:maps_to_has_type_reflect.
      + intros. edestruct fill_derivative as [h [d' [A [B C]]]]; eauto.
        sinvert A.
        assert (p = p0) by scongruence.
        assert (s' = s'0) by sfirstorder use:derivative_det.
        sfirstorder.
      + qauto l: on.
  (* par-R *)
  - edestruct IHStep1 as [A [B [C L]]]; eauto.
    edestruct IHStep2 as [A' [B' [C' L']]]; eauto.
    split; try split; try split.
    + sauto lq: on.
    + intros. sinvert H4. econstructor; eauto. sfirstorder.
    + sfirstorder.
    + intros.
  (* cat-R-1 *)
  - edestruct IHStep as [A [B [C L]]]; eauto.
    sinvert H2.
    sinvert H3.
    destruct H11;[|shelve].
    split; try split; try split.
    + sauto lq: on.
    + intros. sinvert H4. sinvert H3. assert (H00 : D = D') by best use:context_derivative_emp'. rewrite -> H00 in *. econstructor. eauto. eauto. assert (~(Nullable s'0)). { intro. assert (MaximalPrefix p).  eapply maximal_derivative_nullable'; eauto. sfirstorder. } sfirstorder.
    + intros. sfirstorder.
    + intros. sfirstorder.
    Unshelve.
    assert (MaximalOn (fv e1) n). { eapply prop_on_contains. eapply typing_fv. eauto. eauto. }
    assert (MaximalPrefix p) by sauto lq: on.
    best.

  (* Cat-R-2 *)
  - edestruct IHStep1 as [A [B C]]; eauto.
    edestruct IHStep2 as [A' [B' C']]; eauto.
    split; try split; try split.
    + hauto l: on.
    + intros. sinvert H5. sinvert H6. eapply TSubCtx; [|eauto]. hauto l: on.
    + intros. sfirstorder.
    + intros H00 H01. rewrite -> H00 in *. unfold inert_guard in *.
      edestruct H2 as [UU UU']; eauto; eauto.
      rewrite -> UU in *.
      assert (EmptyOn (fv e1) n) by best use:prop_on_contains.
      assert (EmptyPrefix p1) by best.
      assert (Nullable s) by best use:hmm''.
      best.
    
  - assert (H00 : PrefixTyped (PfxParPair p1 p2) (TyPar s t)) by hauto l: on use: maps_to_has_type_reflect.
    sinvert H00. edestruct IHStep as [A [B C]]; clear IHStep.
    + eassumption.
    + eapply wf_hole_iff in H6 as [Hh [Hc Hd]]; [| eassumption].
      eapply wf_hole_iff; [eassumption |].
      repeat split; [assumption | constructor; constructor | |]; sfirstorder.
    + admit.
    + repeat split.
      * sfirstorder.
      * intros. edestruct fill_derivative as [G' [zst' [A' [B' [C' D']]]]];
        [| eassumption |]; [eassumption |]. sinvert A'. sinvert H17.
        assert (p0 = p1) by congruence. assert (p3 = p2) by congruence. subst.
        specialize (D' (CtxComma (CtxHasTy x s) (CtxHasTy y t))).
        specialize (D' (CtxComma (CtxHasTy x s'1) (CtxHasTy y t'))).
        specialize (D' Gxsyt (env_union (singleton_env x p1) (singleton_env y p2))).
        edestruct D' as [u [A'' B'']]; [eassumption | | |].
        -- admit. (* need a smart constructor here *)
        -- eapply context_derivative_comma; try (eapply context_derivative_sng; eassumption).
           intro test. cbn. destruct (eqb_spec x test); destruct (eqb_spec y test); sfirstorder.
        -- admit.
      * admit. (* todo: will: figure out the lemma that needs to go here, from the pareserves i (env_union ...) to the goal. *)
      * admit.
  - admit.
  - assert (H00 : PrefixTyped (PfxCatBoth p1 p2) (TyDot s t)) by best use:maps_to_has_type_reflect.
    sinvert H00. edestruct IHStep as [A [B C]]. eauto. eauto. eapply catrenvtyped2; eauto.
    split; try split.
    + sfirstorder.
    + intros. edestruct fill_derivative as [G' [zst' [A' [B' [C' D']]]]]; eauto.
      sinvert A'.
      destruct (ltac:(scongruence) : (PfxCatBoth p1 p2) = p).
      sinvert H18.
      edestruct (derivative_fun p1 s) as [s'']; eauto.
      specialize (D' (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) (CtxSemic (CtxHasTy x s'') (CtxHasTy y s'0)) Gxsyt (env_union (singleton_env x p1) (singleton_env y p2))).
      edestruct D' as [u [A'' B'']]. eauto. admit. eapply context_derivative_semic; [admit | |]; eapply context_derivative_sng; eauto.
      specialize (B u s').
      edestruct (fill_reflect_fun G' (CtxSemic CtxEmpty (CtxHasTy z s'0))) as [g''].
      eapply (TSubCtx g' g''); [ eapply (SubCong G'); eauto |].

      eapply (TLet (hole_compose G' (HoleSemicL HoleHere (CtxHasTy z s'0))) CtxEmpty (fill G' (CtxSemic (CtxHasTy x s'') (CtxHasTy z s'0)))).
        admit. (* todo: will: theorem about hole compose free variables should be union. *)
        sfirstorder use:sink_tm_typing.
        admit. (* best use:hole_compose_fill,reflect_fill. *)
        admit. (* this used to work: best use:hole_compose_fill. *)
        eapply (typing_subst (hole_compose G' (HoleSemicR (CtxHasTy x s'') HoleHere))). eauto. { eapply context_derivative_wf; [|eauto]; eauto. } admit. admit. admit.
    + admit.
  - edestruct (IHStep1) as [A [B [U V]]]; eauto.
   (* todo: need better automation for disjoitnness *)
    assert (NoConflictOn eta (singleton_env x p) (fv G)). { eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. intros. intro. assert (x0 <> x) by scongruence. assert (x = x0) by qauto l: on use:dom_singleton. sfirstorder. }
    assert (EnvTyped (env_subst x p eta) Gxs). eapply env_subctx_bind'; [ | eauto | eauto | | | ]. eauto. eauto. { eapply env_typed_singleton. eauto. } { eapply preserves_to_agree. eapply typing_fv; eauto. sfirstorder. }
    edestruct (wf_fill_reflect G) as [QQ _]; eauto.
    assert (WFContext Gxs). { eapply wf_fill_reflect. eauto. best use:DisjointSets_inj'. }
    edestruct IHStep2 as [A' [B' [U' V']]]; eauto.
    split; try split; try split.
    + eauto.
    + intros GD' t'. intros.
      edestruct (fill_derivative eta G D GD GD') as [G' [D' [L [M [N O]]]]]; eauto.
      edestruct (derivative_fun p) as [s']; eauto.
      assert (Typed D' NoRec e1' s' Inert) by hauto l: on.
      edestruct (O (CtxHasTy x s) (CtxHasTy x s') Gxs (singleton_env x p)) as [G'xs' [W X]]. eauto. eauto. hauto l: on.
      econstructor; [ | eauto | | eauto | ]. hauto q:on use:fv_hole_derivative. eauto.
      eapply B'; eauto. 
    + intros. assert (MaximalOn (set_minus (fv e2) (singleton_set x)) eta) by hauto q: on.
      eapply U'. eapply prop_on_minus. eapply U. hauto q: on. eauto.
    + intros. assert (EmptyOn (set_minus (fv e2) (singleton_set x)) eta) by hauto q: on.
      eapply V'. eauto. eapply prop_on_minus. eapply V. eauto. hauto q: on. eauto.
  - split; try split; try split.
    + best use:emp_well_typed.
    + intros.
      assert (Derivative (emp r) r r) by best use:derivative_emp.
      destruct (ltac:(sfirstorder use:derivative_det) : r = s').
      edestruct (env_cat_exists_when_typed eta') as [eta''0 [A [B C]]]; eauto.
      destruct (ltac:(hauto l:on use:env_cat_unique) : eta'' = eta''0).
      eapply TPlusCase; eauto. 
    + assert (Subset (singleton_set z) (fv (TmPlusCase eta' r z x e1 y e2))) by sfirstorder.
      intro HM. eapply (prop_on_contains) in HM; [|eauto].
      edestruct (env_cat_maximal (singleton_set z) eta' eta eta''); eauto. { admit. } { admit. }
      assert (Hcontra : MaximalPrefix PfxSumEmp) by best.
      sinvert Hcontra.
    + best use:emp_empty.
  - assert (WFContext Gz) by sfirstorder use:context_derivative_wf'.
    assert (Hwf : WFHole G /\ DisjointSets (fv G) (singleton_set z)) by sauto use:wf_fill_reflect.
    destruct Hwf.
    assert (~ fv G z) by sfirstorder.
    assert (WFHole G). { eapply (wf_fill_reflect G (CtxHasTy z _)). eauto. sfirstorder use:context_derivative_wf'. }
    edestruct (env_cat_exists_when_typed eta') as [eta''0 [A [B C]]]; eauto.
    destruct (ltac:(sfirstorder use:env_cat_unique) : eta'' = eta''0).
    assert (Hty : exists p0, eta'' z = Some p0 /\ PrefixTyped p0 (TySum s t)) by best use:maps_to_has_type_reflect.
    edestruct Hty as [p0 [L M]].
    destruct (ltac:(scongruence) : PfxSumInl p = p0).
    sinvert M.
    edestruct IHStep as [A' [B' [C' D']]]. eauto. { eapply wf_fill_reflect. eauto. sfirstorder. } { eapply sumcaseenvtyped1; eauto. }
    split; try split; try split.
    + eauto.
    + intros.
      edestruct (fill_derivative eta'' G (CtxHasTy z (TySum s t))) as [G' [d_s [A'' [B'' [C'' D'']]]]]; [eauto | eapply C; eauto |]. 
      sinvert A''.
      destruct (ltac:(scongruence) : PfxSumInl p = p0).
      sinvert H25.
      assert (WFContext Gx). { eapply wf_fill_reflect. eauto. hauto drew: off. }
      edestruct (D'' (CtxHasTy x s) (CtxHasTy x s'0) Gx (singleton_env x p)) as [Gx' [U V]]. eauto. { eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. intros. admit. } eapply context_derivative_sng; eauto.
      eapply (typing_subst G'); [ | | | eauto | eauto ]. { eapply B'; eauto. } { hauto l: on use:context_derivative_wf. } { hauto q: on use:fv_hole_derivative. }
    + intros.
      assert (MaximalOn (set_union (set_minus (fv e1) (singleton_set x)) (singleton_set z)) eta) by hfcrush use:prop_on_contains.
      assert (MaximalOn (set_union (set_minus (fv e1) (singleton_set x)) (singleton_set z)) eta''). eapply env_cat_maximal; [ eauto | | | ]. admit. admit. hauto lq: on rew: off.
      edestruct (H20 z) as [p00 [L' R]]. hauto lq: on rew: off.
      destruct (ltac:(scongruence) : PfxSumInl p = p00).
      sinvert R.
      eapply C'. eapply prop_on_minus. eauto. qauto l: on.
    + intros.
      assert (eta' z = Some PfxSumEmp) by sfirstorder.
      assert (EmptyOn (singleton_set z) eta) by hauto q: on use:prop_on_contains.
      assert (EmptyOn (singleton_set z) eta''). eapply env_cat_empty'; [eauto | sauto].
      edestruct (H22 z) as [p'' []]; eauto.
      destruct (ltac:(scongruence) : PfxSumInl p = p'').
      sinvert H24.
  - admit.
Admitted.





(* this is basically how this theorem needs to go, but we have to figure out how to tie the knot with the regular soundness theorem. *)
Theorem soundargs : forall g_in e g_out g_out' eta_in e' eta_out i,
    ArgsStep eta_in g_out e e' g_out' eta_out ->
    P_sound_args g_in i e g_out eta_in e' g_out' eta_out.
Proof.
  intros.
  generalize dependent g_in.
  generalize dependent i.
  induction H; unfold P_sound_args in *; intros.
  - best.
  - sinvert H1. 
    edestruct sound as [A [B C]]; eauto.
  split; try split; try split.
    + eapply env_typed_singleton; eauto.
    + sfirstorder use:dom_singleton.
    + sfirstorder use:dom_singleton.
    + eapply preserves_to_agree; [| hauto lq: on rew: off ]. hauto l: on use:typing_fv.
    + sauto lq: on.
  - sinvert H1. sinvert H2.
    edestruct IHArgsStep1 as [A [B [C D]]]; eauto.
    edestruct IHArgsStep2 as [E [F [G L]]]; eauto.
    split; try split; try split; try split.
    + eapply env_typed_comma; [| eauto | eauto]. hauto q: on.
    + hauto q: on.
    + hauto drew: off.
    + intros. assert (fv (CtxComma g1 g2) = set_union (fv g1) (fv g2)) by best. rewrite -> H2 in *. eapply prop_on_set_union. split.
      * eapply prop_on_weakening_alt'. eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. qauto l: on use:empty_env_for_dom.
        hauto q: on.
      * admit.
    + intros. edestruct i; try scongruence. assert (H00 : i1 = Inert /\ i2 = Inert) by best use:i_ub_inert. destruct H00 as [UU UU']. rewrite -> UU in *. rewrite -> UU' in *. admit.
    + intros; econstructor; eauto. sfirstorder.
  - sinvert H1; sinvert H2; sinvert H4; sinvert H3.
    edestruct IHArgsStep as [A [B [C D]]]; eauto.
    split; try split; try split; try split.
    + eapply env_typed_semic; [| eauto| sfirstorder use:empty_env_for_typed | hauto lq: on use:empty_env_for_empty_on] . 
      clear D; clear C; clear H13; clear H9; clear H11; clear H; clear H0; clear IHArgsStep.
      assert (Subset (fv g1) (dom eta1)) by best use:envtyped_dom.
      assert (Subset (fv g0) (dom eta)) by best use:envtyped_dom.
      hauto lq:on rew: off use:empty_env_for_dom.
    + cbn. hauto q: on use:empty_env_for_dom.
    + cbn. hauto q: on use:empty_env_for_dom.
    + intros. sfirstorder.
    + intros H00 H01. rewrite -> H00 in *.
      unfold inert_guard in *. assert (i1 = Inert) by best. rewrite -> H1 in *.
      assert (H02 : fv (CtxSemic g1 g2) = set_union (fv g1) (fv g2)) by best. rewrite -> H02 in *. eapply prop_on_set_union. split.
      * eapply prop_on_weakening_alt'. eapply no_conflict_on_disjoint. right. eapply DisjointSets_inj. qauto l: on use:empty_env_for_dom.
        hauto q: on.
      * eapply prop_on_weakening. hauto q: on use:empty_env_for_empty_on.
    + intros. sinvert H1.
      destruct H12.
      *  assert (H00 : D' = g3) by best use:context_derivative_emp'.
         rewrite <- H00 in *.
         econstructor; eauto.
         assert (~(MaximalOn (fv g0) eta)) by best.
         unfold inert_guard in *.
         intros. split. auto.
         admit. (* TODO: need a new theorem about nullable derivatives *)
      (* contradictory. *)
      * sfirstorder.
  - sinvert H2. sinvert H3. sinvert H5. sinvert H4.
    edestruct IHArgsStep1 as [A [B [C D]]]; eauto.
    edestruct IHArgsStep2 as [E [F [G H']]]; eauto.
    split; try split; try split; try split.
    + eapply env_typed_semic; [| eauto | eauto | eauto]. hauto q: on.
    + hauto q: on.
    + hauto drew: off.
    + intros. admit.
    + intros H00 H01; rewrite -> H00 in *. unfold inert_guard in *. assert (H02 : i1 = Inert) by best. rewrite -> H02 in *.
      assert (H03 : fv (CtxSemic g1 g2) = set_union (fv g1) (fv g2)) by best. rewrite -> H03 in *. 
      assert (H04 : fv (CtxSemic g0 g3) = set_union (fv g0) (fv g3)) by best. rewrite -> H04 in *. 
      assert (EmptyOn (fv g0) eta) by best use:prop_on_set_union.
      assert (EmptyOn (fv g3) eta) by best use:prop_on_set_union.
      eapply prop_on_set_union. split.
      * eapply prop_on_weakening_alt';[|qauto l: on]. eapply no_conflict_on_disjoint. right. best use:empty_env_for_dom.
      * eapply prop_on_weakening. unfold Agree in G. admit.
    + intros. sinvert H2. econstructor. eauto. eauto. scongruence.
Admitted.
