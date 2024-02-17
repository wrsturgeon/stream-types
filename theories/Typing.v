From Coq Require Import
  Program.Equality
  List
  String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  FV
  Hole
  Sets
  Subcontext
  Terms
  Prefix
  Subst
  SinkTerm
  Inert
  Nullable
  Derivative
  Environment
  RecSig
  History
  Types.

(* TODO:will pull in the rest of the rules (nil, cons, star-case)
   
  if done wiht that, wait (requires histctx)
*)
Inductive Typed : histctx -> context -> recsig -> term -> type -> inertness -> Prop :=
  | TParR : forall G e1 e2 s t i1 i2 i3 rs o,
      Typed o G rs e1 s i1 ->
      Typed o G rs e2 t i2 ->
      i_ub i1 i2 i3 ->
      Typed o G rs (TmComma e1 e2) (TyPar s t) i3
  | TParL : forall G x y z s t e r Gxsyt Gzst i rs o,
      x <> z -> 
      y <> z -> 
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyPar s t)) Gzst ->
      Typed o Gxsyt rs e r i ->
      Typed o Gzst rs (TmLetPar x y z e) r i
  | TCatR : forall G D e1 e2 s t i1 i2 i3 rs o,
      Typed o G rs e1 s i1 ->
      Typed o D rs e2 t i2 ->
      inert_guard (i1 = Inert /\ ~(Nullable s)) i3 ->
      Typed o (CtxSemic G D) rs (TmSemic e1 e2) (TyDot s t) i3
  | TCatL : forall G x y z s t e r Gxsyt Gzst i rs o,
      x <> z -> 
      y <> z -> 
      x <> y ->
      ~ bv_term e z ->
      ~ bv_term e y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyDot s t)) Gzst ->
      Typed o Gxsyt rs e r i ->
      Typed o Gzst rs(TmLetCat t x y z e) r i
  | TEpsR : forall G i rs o,
      Typed o G rs TmSink TyEps i
  | TOneR : forall G rs o,
      Typed o G rs TmUnit TyOne Jumpy
  | TVar : forall G x s Gxs i rs o,
      Fill G (CtxHasTy x s) Gxs ->
      Typed o Gxs rs (TmVar x) s i
  | TLet : forall G D Gxs x e e' s t GD i rs o,
      ~fv G x ->
      ~fv D x ->
      Typed o D rs e s Inert ->
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      Typed o Gxs rs e' t i ->
      Typed o GD rs (TmLet x e e') t i
  | TInl : forall G e s t i rs o,
      Typed o G rs e s i ->
      Typed o G rs (TmInl e) (TySum s t) Jumpy
  | TInr : forall G e s t i rs o,
      Typed o G rs e t i ->
      Typed o G rs (TmInr e) (TySum s t) Jumpy
  | TPlusCase : forall G x y z s t r Gz Gx Gy Gz' e1 e2 eta i i1 i2 rs o,
      x <> z ->
      y <> z ->
      ~ fv G x ->
      ~ fv G y ->
      ~ bv_term e1 z ->
      ~ bv_term e2 z ->
      ~ bv_term e1 x ->
      ~ bv_term e2 y ->
      Fill G (CtxHasTy z (TySum s t)) Gz ->
      Fill G (CtxHasTy x s) Gx ->
      Fill G (CtxHasTy y t) Gy ->
      EnvTyped eta Gz ->
      ContextDerivative eta Gz Gz' ->
      Typed o Gx rs e1 r i1 ->
      Typed o Gy rs e2 r i2 ->
      inert_guard (eta z = Some PfxSumEmp) i ->
      Typed o Gz' rs (TmPlusCase eta r z x e1 y e2) r i
  | TNil : forall o G rs s,
      Typed o G rs TmNil (TyStar s) Jumpy
  | TCons : forall G D e1 e2 s i1 i2 rs o,
      Typed o G rs e1 s i1 ->
      Typed o D rs e2 (TyStar s) i2 ->
      Typed o (CtxSemic G D) rs (TmCons e1 e2) (TyStar s) Jumpy
  | TRec : forall G G' s i args o o' hpargs,
      HistArgsTyped o hpargs o' ->
      ArgsTyped o G' (Rec o' G s i) args G i ->
      Typed o G' (Rec o' G s i) (TmRec args hpargs) s i
  | TFix : forall G G' rs args e r i o o' hpargs,
      WFContext G ->
      HistArgsTyped o' hpargs o ->
      ArgsTyped o' G' rs args G i ->
      Typed o G (Rec o G r i) e r i ->
      Typed o' G' rs (TmFix args hpargs G r e) r i
  | TmArgsLet : forall G G' args e rs s i o,
      WFContext G ->
      ArgsTyped o G' rs args G i ->
      Typed o G rs e s i ->
      Typed o G' rs (TmArgsLet args G e)  s i
  | TmHistPgm : forall G rs hp s o,
      HistTyped o hp (flatten_type s) ->
      Typed o G rs (TmHistPgm hp s) s Jumpy
  | TWait : forall G Gz Gz' Gemp z s r i i' e rs eta o,
      Fill G (CtxHasTy z s) Gz ->
      EnvTyped eta Gz ->
      ContextDerivative eta Gz Gz' ->
      Fill G CtxEmpty Gemp ->
      Typed (cons (flatten_type s) o) Gemp rs e r i ->
      inert_guard ((forall p, eta z = Some p -> ~ MaximalPrefix p) /\ ~Nullable s) i' ->
      Typed o Gz' rs (TmWait eta r s z e) r i'
  | TSubCtx : forall G G' e s i rs o,
      Subcontext G G' ->
      Typed o G' rs e s i ->
      Typed o G rs e s i
      
with ArgsTyped : histctx -> context -> recsig -> argsterm -> context -> inertness -> Prop :=
  | T_ATmEmpty : forall g rs i o, ArgsTyped o g rs ATmEmpty CtxEmpty i
  | T_ATmSng : forall g rs e s x i o,
      Typed o g rs e s i ->
      ArgsTyped o g rs (ATmSng e) (CtxHasTy x s) i
  | T_ATmComma : forall g g1 g2 e1 e2 rs i1 i2 i3 o,
      ArgsTyped o g rs e1 g1 i1 ->
      ArgsTyped o g rs e2 g2 i2 ->
      i_ub i1 i2 i3 ->
      ArgsTyped o g rs (ATmComma e1 e2) (CtxComma g1 g2) i3
  | T_ATmSemic1 : forall g1 g2 g1' g2' e1 e2 rs i1 i2 i3 o,
      ArgsTyped o g1 rs e1 g1' i1 ->
      ArgsTyped o g2 rs e2 g2' i2 ->
      inert_guard (i1 = Inert /\ ~(NullableCtx g1')) i3 ->
      ArgsTyped o (CtxSemic g1 g2) rs (ATmSemic1 e1 e2) (CtxSemic g1' g2') i3
  | T_ATmSemic2 : forall g1 g2 g1' g2' e2 rs i o,
      NullableCtx g1' ->
      ArgsTyped o g2 rs e2 g2' i ->
      ArgsTyped o (CtxSemic g1 g2) rs (ATmSemic2 e2) (CtxSemic g1' g2') i
.


Scheme Typed_ind' := Induction for Typed Sort Prop
with ArgsTyped_ind' := Induction for ArgsTyped Sort Prop.
Combined Scheme Typed_mutual from Typed_ind', ArgsTyped_ind'.

Hint Constructors Typed : core.
Hint Constructors ArgsTyped : core.

Check Typed_mutual.

Theorem typing_fix_subst_mut :
  (forall o' (g' : context) (rs: recsig) e' t i', Typed o' g' rs e' t i' -> 
    forall o g e s i,
      Typed o g (Rec o g s i) e s i ->
      WFContext g ->
      rs = Rec o g s i ->
      Typed o' g' NoRec (fix_subst g s e e') t i') /\
  (forall o' g' (rs: recsig) args g'' i', ArgsTyped o' g' rs args g'' i' ->
    forall o g e s i,
      Typed o g (Rec o g s i) e s i ->
      WFContext g ->
      rs = Rec o g s i ->
      ArgsTyped o' g' NoRec (fix_subst_args g s e args) g'' i').
intros.
  apply Typed_mutual; cbn; intros.
  - econstructor. { eapply H; eauto. } { eapply H0; eauto. } hauto l: on.
  - hauto l: on.
  - hecrush.
  - econstructor. best. best. best. best use:bv_fixsubst. best use:bv_fixsubst. best. best. best. best. best.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - hauto l: on.
  - hauto l: on.
  - hauto l: on.
  - econstructor; hauto q: on use:bv_fixsubst. 
  - econstructor; hauto q:on use:bv_fixsubst.
  - cbn. econstructor;sfirstorder.
  - hauto l: on.
  - hauto l: on.
  - hauto l: on.
  - hauto l: on.
  - econstructor; sfirstorder.
  - hauto l: on.
  - hauto l: on.
  - sauto lq: on.
  - intros. econstructor. { eapply H; eauto. } { eapply H0; eauto. } sfirstorder.
  - intros. econstructor. { eapply H; eauto. } { eapply H0; eauto. } sfirstorder.
  - hauto l: on.
Qed.

Theorem typing_fix_subst : forall g g' e e' s t i i' o o',
  WFContext g ->
  Typed o g (Rec o g s i) e s i ->
  Typed o' g' (Rec o g s i) e' t i' -> 
  Typed o' g' NoRec (fix_subst g s e e') t i'.
Proof.
sfirstorder use:typing_fix_subst_mut.
Qed.




Theorem fv_hole_minus : forall GD,
  WFContext GD ->
  forall G D,
  Fill G D GD ->
  SetEq (fv G) (set_minus (fv GD) (fv D)).
Proof.
  intros GD Hw G D Hf. generalize dependent GD. generalize dependent D.
  induction G; cbn in *; intros.
  - sinvert Hf. split; tauto.
  - sinvert Hf. sinvert Hw. eassert (A := IHG _ _ H1 H3). split; intros.
    2: { repeat destruct H. { right. apply A. split; assumption. } left. assumption. }
    split. { destruct H. { right. assumption. } apply A in H as [H _]. left. assumption. }
    intro C. destruct H; [| apply A in H; tauto].
    assert (H0 := H1). eapply wf_hole_iff in H0 as [Hh [HD Hd]]; [| eassumption].
    apply fv_fill in H3. apply H4 in H. apply H. apply H3. left. assumption.
  - sinvert Hf. sinvert Hw. eassert (A := IHG _ _ H2 H3). split; intros.
    2: { repeat destruct H. { left. assumption. } right. apply A. split; assumption. }
    split. { destruct H. { left. assumption. } apply A in H as [H _]. right. assumption. }
    intro C. destruct H; [| apply A in H; tauto].
    apply fv_fill in H3. apply H4 in H; [destruct H |]. apply H3. left. assumption.
  - sinvert Hf. sinvert Hw. eassert (A := IHG _ _ H1 H3). split; intros.
    2: { repeat destruct H. { right. apply A. split; assumption. } left. assumption. }
    split. { destruct H. { right. assumption. } apply A in H as [H _]. left. assumption. }
    intro C. destruct H; [| apply A in H; tauto].
    assert (H0 := H1). eapply wf_hole_iff in H0 as [Hh [HD Hd]]; [| eassumption].
    apply fv_fill in H3. apply H4 in H. apply H. apply H3. left. assumption.
  - sinvert Hf. sinvert Hw. eassert (A := IHG _ _ H2 H3). split; intros.
    2: { repeat destruct H. { left. assumption. } right. apply A. split; assumption. }
    split. { destruct H. { left. assumption. } apply A in H as [H _]. right. assumption. }
    intro C. destruct H; [| apply A in H; tauto].
    apply fv_fill in H3. apply H4 in H; [destruct H |]. apply H3. left. assumption.
Qed.
Hint Resolve fv_hole_minus : core.

(* (P : ∀ (c : context) (t : term) (t0 : type) (i : inertness),
       Typed c t t0 i → Prop) *)

Definition P_typing_fv (o : histctx) (g : context) (rs : recsig) (e : term) (s : type) (i : inertness) :=
  forall x, fv e x -> fv g x.
Arguments P_typing_fv o g rs e s i/.

Definition P_argstyping_fv (o : histctx) (g : context) (rs : recsig) (args : argsterm) (g' : context) (i : inertness) :=
  forall x, fv args x -> fv g x.
Arguments P_argstyping_fv o g rs args g' i/.

(* TODO: will: priority *)
Theorem typing_fv' :
  (forall o g rs e s i, Typed o g rs e s i -> P_typing_fv o g rs e s i) /\
  (forall o g rs args g' i, ArgsTyped o g rs args g' i -> P_argstyping_fv o g rs args g' i).
Proof.
  apply Typed_mutual; cbn in *; intros.
 - sfirstorder.
 - apply (fv_fill _ _ _ f0). cbn. destruct H0 as [| [[Hfx Hx] Hy]]. { left. assumption. }
   apply H in Hfx. apply (fv_fill _ _ _ f) in Hfx. cbn in Hfx.
   destruct Hfx. { destruct H0; subst; contradiction. }
   right. assumption.
 - sfirstorder.
 - apply (fv_fill _ _ _ f0). cbn. destruct H0 as [| [[Hfx Hx] Hy]]. { left. assumption. }
   apply H in Hfx. apply (fv_fill _ _ _ f) in Hfx. cbn in Hfx.
   destruct Hfx. { destruct H0; subst; contradiction. }
   right. assumption.
 - sfirstorder.
 - sfirstorder.
 - hauto q: on use:fv_fill.
 - apply (fv_fill _ _ _ f0). cbn. destruct H1 as [He | [He' Hx]]. { left. apply H. assumption. }
   right. apply H0 in He'. apply (fv_fill _ _ _ f) in He'.
   cbn in He'. destruct He'. { contradiction Hx. } assumption.
 - sfirstorder.
 - sfirstorder.
 - repeat destruct H1.
   + hauto q: on use:fv_context_derivative,fv_fill.
   + eapply (fv_context_derivative eta Gz). eauto. eapply fv_fill. eauto. right.
     eapply H in H1. qauto use:fv_fill.
   + eapply (fv_context_derivative eta Gz). eauto. eapply fv_fill. eauto. right.
     eapply H0 in H1. qauto use:fv_fill.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder.
 - hauto q:on use:fv_fill, fv_context_derivative.
 - sfirstorder use:subcontext_fv_subset.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder.
Qed.


Theorem typing_fv : forall G e s i rs o,
  Typed o G rs e s i ->
  Subset (fv e) (fv G).
Proof.
best use:typing_fv'.
Qed.

Theorem typing_fv_args : forall G G' e i rs o,
  ArgsTyped o G rs e G' i ->
  Subset (fv e) (fv G).
Proof.
best use:typing_fv'.
Qed.

Hint Resolve typing_fv : core.

Theorem sink_tm_typing : forall g p s s' rs o,
  PrefixTyped p s ->
  MaximalPrefix p ->
  Derivative p s s' ->
  Typed o g rs (sink_tm p) s' Inert.
Proof.
intros g p s s' rs o Ht Hm.
generalize dependent s'.
generalize dependent g.
generalize dependent rs.
generalize dependent o.
dependent induction Ht; sinvert Hm; cbn; intros o rs g s' Hd.
- best.
- best.
- sinvert Hd. econstructor; sfirstorder.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
Qed.

Theorem typing_histval_subst : 
  (forall o g rs e s i, Typed o g rs e s i -> forall ts t ts' v n, o = app ts (cons t ts') -> Datatypes.length ts = n -> HistValTyped v t -> Typed (app ts ts') g rs (histval_subst v n e) s i) /\ 
  (forall o g rs args g' i, ArgsTyped o g rs args g' i -> forall ts t ts' v n, o = app ts (cons t ts') -> Datatypes.length ts = n -> HistValTyped v t -> ArgsTyped (app ts ts') g rs (histval_subst_args v n args) g' i).
Proof.
  apply Typed_mutual; intros.
  - cbn. econstructor. eauto. eauto. sfirstorder.
  - hauto drew: off.
  - sblast.
  - econstructor. best. best. best. best use:bv_histval_subst. best use:bv_histval_subst. best. best. best. best. best.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - econstructor. sfirstorder. sfirstorder. sfirstorder. sfirstorder. hauto q:on use:bv_histval_subst. hauto q: on use:bv_histval_subst. hauto q: on use:bv_histval_subst. hauto q: on use:bv_histval_subst. sfirstorder. sfirstorder. sfirstorder. sfirstorder. sfirstorder. sfirstorder. sfirstorder. sfirstorder.
  - hauto drew: off.
  - cbn. econstructor; sfirstorder.
  - best use:histval_subst_histargs_thm.
  - hauto l: on use:histval_subst_histargs_thm.
  - hauto l: on.
  - sfirstorder use: histval_subst_hist_thm.
  - cbn.
    assert (H00 : cons (flatten_type s) (app ts ts') = app (cons (flatten_type s) ts) ts') by scongruence.
    econstructor; hauto lq: on drew: off.
  - hauto l: on.
  - sfirstorder use: histval_subst_histargs_thm.
  - hauto l:on use: histval_subst_histargs_thm.
  - cbn. econstructor; eauto.
  - cbn. econstructor; eauto.
  - cbn. econstructor; eauto.
Qed.

Theorem typing_histval_subst_all : 
  forall ts g rs e s i vs,
    Typed ts g rs e s i ->
    HistValAllTyped vs ts ->
    Typed nil g rs (histval_subst_all vs e) s i.
Proof.
  intros; generalize dependent e; generalize dependent rs; generalize dependent g; generalize dependent s; generalize dependent i.
  induction H0; intros.
  - hauto q: on.
  - cbn. eapply IHHistValAllTyped. 
    assert (H00 : ts = app nil ts) by scongruence. rewrite -> H00.
    hauto lq: on rew: off use: typing_histval_subst.
Qed.

Theorem typing_subst :
  (forall o G rs e t i, Typed o G rs e t i ->
    forall x y,
      WFContext G ->
      ~ fv G x ->
      ~ bv_term e x ->
      ~ bv_term e y ->
      (forall G', CtxSubst x y G G' -> Typed o G' rs (subst_var e x y) t i) /\ 
      (~fv e y -> Typed o G rs (subst_var e x y) t i)) /\

  (forall o G rs e G0 i, ArgsTyped o G rs e G0 i ->
    forall x y,
      WFContext G ->
      ~ fv G x ->
      ~ bv_argsterm e x ->
      ~ bv_argsterm e y ->
      (forall G', CtxSubst x y G G' -> ArgsTyped o G' rs (subst_var_argsterm e x y) G0 i) /\
      (~fv e y -> ArgsTyped o G rs (subst_var_argsterm e x y) G0 i)
      ).
Proof.
  apply Typed_mutual; intros; cbn.
  (* par-r *)
  - edestruct H as [U V]. eauto. eauto. best. best.
    edestruct H0 as [U' V']. eauto. eauto. best. best.
    split; intros.
    + econstructor. best. best. best.
    + econstructor. best. best. best.
  (* par-l *)
  - cbn.
    assert (WFContext Gxsyt). { eapply wf_fill_reflect. eauto. split. sfirstorder use:wf_fill_reflect. split. sauto. eapply DisjointSets_inj'. intros x1 H00. cbn in H00. destruct H00; scongruence. }
    assert (~fv Gxsyt x0). { intro H00. eapply fv_fill in H00;[|eauto]. cbn in H00. destruct H00;[sfirstorder|]. hauto q: on use:fv_fill. }
    edestruct (H x0 y0). eauto. { intro. assert (H00 : fv G x0 \/ x = x0 \/ y = x0) by qauto use:fv_fill. destruct H00 as [A | [B | C]]; [|sfirstorder|sfirstorder]. hauto q: on use:fv_fill. } sfirstorder. sfirstorder.
    split; intros.
    -- edestruct (ctx_subst_fill_arb G (CtxHasTy z (TyPar s t))) as [[G'00 [U [V W]]] | [D' [U V]]]. eauto. eauto.
       + assert (z <> y0) by sfirstorder use:hole_subst_not_in_fill.
         assert (H00 : eqb z y0 = false) by best use:eqb_neq. rewrite -> H00 in *.
         edestruct (W (CtxComma (CtxHasTy x s) (CtxHasTy y t))) as [u [L M]]. eauto.
         assert (WFContext u) by (eapply (ctx_subst_wf x0 y0 Gxsyt); eauto).
         eapply (TParL G'00). scongruence. scongruence. scongruence. hauto q:on use:wf_fill_reflect. hauto q: on use:wf_fill_reflect. sfirstorder. sfirstorder. hauto l: on.
       + sinvert U.
         assert (H00 : eqb z z = true) by best use:eqb_refl; rewrite -> H00 in *.
         econstructor. best. best. best. best. best. best. best. { eapply H6. admit. }
    -- assert (H00 : eqb z y0 = false) by best use:eqb_neq ; rewrite -> H00 in *.
       sfirstorder.
  (* cat-r *)
  - edestruct (H x y) as [U V]. sauto lq: on rew: off. sfirstorder. sfirstorder. sfirstorder.
    edestruct (H0 x y) as [W X]. sauto lq: on rew: off. sfirstorder. sfirstorder. sfirstorder.
    sinvert H1.
    split; intros; cbn.
    -- sinvert H1.
       + econstructor. best. eapply X. { intro. eapply typing_fv in H1;[|eauto]. hauto q: on use:ctx_subst_found_fv. } best.
       + econstructor. { eapply V. intro. eapply typing_fv in H1;[|eauto]. hauto q: on use:ctx_subst_found_fv. } sfirstorder. sfirstorder.
    -- econstructor; sfirstorder.
  (* cat-l *)
  - cbn.
    assert (WFContext Gxsyt). { eapply wf_fill_reflect. eauto. split. sfirstorder use:wf_fill_reflect. split. sauto. eapply DisjointSets_inj'. intros x1 H00. cbn in H00. destruct H00; scongruence. }
    assert (~fv Gxsyt x0). { intro H00. eapply fv_fill in H00;[|eauto]. cbn in H00. destruct H00;[sfirstorder|]. hauto q: on use:fv_fill. }
    edestruct (H x0 y0). eauto. { intro. assert (H00 : fv G x0 \/ x = x0 \/ y = x0) by qauto use:fv_fill. destruct H00 as [A | [B | C]]; [|sfirstorder|sfirstorder]. hauto q: on use:fv_fill. } sfirstorder. sfirstorder.
    split; intros.
    -- edestruct (ctx_subst_fill_arb G (CtxHasTy z (TyDot s t))) as [[G'00 [U [V W]]] | [D' [U V]]]. eauto. eauto.
       + assert (z <> y0) by sfirstorder use:hole_subst_not_in_fill.
         assert (H00 : eqb z y0 = false) by best use:eqb_neq. rewrite -> H00 in *.
         edestruct (W (CtxSemic (CtxHasTy x s) (CtxHasTy y t))) as [u [L M]]. eauto.
         assert (WFContext u) by (eapply (ctx_subst_wf x0 y0 Gxsyt); eauto).
         eapply (TCatL G'00). scongruence. scongruence. scongruence. sfirstorder use:bv_var_subst. sfirstorder use:bv_var_subst. hauto q: on use:wf_fill_reflect. hauto q: on use:wf_fill_reflect. sfirstorder. sfirstorder. hauto l: on.
       + sinvert U.
         assert (H00 : eqb z z = true) by best use:eqb_refl; rewrite -> H00 in *.
         econstructor. sfirstorder. sfirstorder. sfirstorder. sfirstorder use:bv_var_subst. sfirstorder use:bv_var_subst. best. best. best. best. { eapply H7. admit. }
    -- assert (H00 : eqb z y0 = false) by best use:eqb_neq ; rewrite -> H00 in *.
       econstructor. sfirstorder. sfirstorder. sfirstorder. sfirstorder use:bv_var_subst. sfirstorder use:bv_var_subst. eauto. eauto. eauto. eauto. sfirstorder.
  (* oner *)
  - sfirstorder.
  (* epsr *)
  - sfirstorder.
  (* var *)
  - cbn.
    assert (H00 : x = y \/ x <> y) by sfirstorder use:string_dec.
    split; intros.
    + destruct H00.
      * rewrite -> H4 in *.
        assert (eqb y y = true) by best use:eqb_refl.
        rewrite -> H5 in *. econstructor; eapply ctx_subst_fill_transport; eauto. 
      * assert (eqb x y = false) by best use:eqb_neq. rewrite -> H5 in *.
        edestruct ctx_subst_fill_other_hole as [h']; eauto.
    + destruct (ltac:(sfirstorder use:eqb_neq) : false = eqb x y). sfirstorder.
  (* cut *)
  - edestruct (H x0 y) as [A B]. admit. admit. best. best.
    edestruct (H0 x0 y) as [A' B']. admit. admit. best. best.
    split; intros.
    + edestruct (ctx_subst_fill_arb G D) as [[G'0 [U [V W]]] | [D' [U V]]]. eauto. eauto.
      * cbn.
        edestruct (W (CtxHasTy x s)) as [G'0x [L M]]. eauto.
        assert (Typed o D rs (subst_var e x0 y) s Inert). eapply B. admit.
        assert (Typed o G'0x rs (subst_var e' x0 y) t i). eapply A'. eauto.
        eapply (TLet G'0 D). { eapply hole_subst_no_found_fv; sfirstorder. } best. best. eauto. sfirstorder. sfirstorder.
      * cbn. 
      assert (Typed o D' rs (subst_var e x0 y) s Inert). eapply A. eauto.
      assert (Typed o Gxs rs (subst_var e' x0 y) t i). eapply B'. admit.
      eapply (TLet G D'); [eauto | eapply ctx_subst_no_found_fv;sfirstorder | eauto | eauto | eauto | eauto]. best.
    + sfirstorder.
  (* inl *)
  - hauto l: on.
  (* inr *)
  - hauto l: on.
  (* pluscase *)
  - admit.
  (* nil *)
  - sfirstorder.
  (* cons *)
  - edestruct (H x y) as [U V]. sauto lq: on rew: off. sfirstorder. sfirstorder. sfirstorder.
    edestruct (H0 x y) as [W X]. sauto lq: on rew: off. sfirstorder. sfirstorder. sfirstorder.
    sinvert H1.
    split; intros; cbn.
    -- sinvert H1.
       + econstructor. best. eapply X. { intro. eapply typing_fv in H1;[|eauto]. hauto q: on use:ctx_subst_found_fv. }
       + econstructor. { eapply V. intro. eapply typing_fv in H1;[|eauto]. hauto q: on use:ctx_subst_found_fv. } sfirstorder.
    -- econstructor; sfirstorder.
  (* tmrec *)
  - hauto l: on.
  (* tmfix *)
  - hauto l: on.
  (* tmargslet *)
  - hauto l: on.
  (* histpgm *)
  - sfirstorder.
  (* wait *)
  - assert (WFContext Gz) by sfirstorder use:context_derivative_wf.
    assert (~fv G x). { intro. assert (~fv Gz x) by hauto q: on use:fv_context_derivative. hauto q: on use:fv_fill. }
    assert (WFContext Gemp) by (eapply wf_fill_reflect; [eauto|sfirstorder use:wf_fill_reflect]).
    edestruct (H x y) as [A0 B0]. eauto. hauto q: on use:fv_fill. scongruence. scongruence.
    split; intros.
    + edestruct (fill_derivative_ctx_subst eta G (CtxHasTy z s)) as [Gz_xy [dD [G'' [B [C [D [E [[Gxy [G''xy [F [I [J K]]]]] | [xyz [U [F [I [J]]]]]]]]]]]]]. eauto. eauto. eauto.
      * sinvert C.
        assert (z <> x). {  assert (~fv Gz x) by hauto q: on use:fv_context_derivative. hauto q: on use:fv_fill. }
        assert (fv G y) by hauto l:on use:hole_subst_found_fv.
        (* assert (y <> z) by sfirstorder. *)
        assert (H00 : eqb z y = false) by admit. rewrite -> H00 in *.
        assert (WFContext Gz_xy). eapply ctx_subst_wf;[| eauto | ]. scongruence use:context_derivative_wf. hauto q: on use:fv_context_derivative.
        edestruct (fill_reflect_fun Gxy CtxEmpty) as [Gxyemp].
        eapply (TWait Gxy). eauto. { eapply env_subst_var_typed';[| | eauto | ]; eauto. }
        { eapply context_derivative_subst_var;[| | | | eauto ]. best use:context_derivative_wf. eauto. eauto. eauto. }
        eauto.
        eapply A0.
        eapply hole_subst_same_fill; [| eauto | eauto ]. eauto.
        { intro H01. rewrite -> H01 in *. split;[|sfirstorder]. intros. unfold env_subst_var in *. admit. }
      * sinvert U. assert (H00 : eqb z z = true) by best use:eqb_refl. rewrite -> H00 in *.
        admit.
    + assert (H00 : eqb z y = false) by best use:eqb_neq. rewrite -> H00 in *.
      assert (H02 : eqb z x = false). { eapply eqb_neq. assert (~fv Gz x) by hauto q:on use:fv_context_derivative. hauto q:on use:fv_fill. }
      econstructor.
      eauto. eapply env_subst_var_nop; hauto q:on use:fv_context_derivative. eapply context_derivative_subst_var_nop; hauto q: on use:fv_context_derivative. eauto. best.
      { intro H01. rewrite -> H01 in *. edestruct i0. eauto. split;[|eauto]. intros. unfold env_subst_var in *. hauto q: on. }
  - edestruct (H x y). sfirstorder use:subtcontext_wf. qauto l: on use:subcontext_fv_subset. best. best.
    split; intros.
    + edestruct subcontext_ctxsubst as [[G'1 [U V]] | [U V]]. eauto. eauto. eauto.
      * eapply TSubCtx. eauto. best.
      * eapply TSubCtx. eauto. eapply H5. qauto l:on use:typing_fv.
    + eapply TSubCtx;sfirstorder.
  - best.
  - best.
  - cbn. split; intros; econstructor; qauto l: on.
  - edestruct H; [sauto lq: on| hauto q:on | sfirstorder | hauto l: on | ].
    edestruct H0; [sauto lq: on rew: off | hauto q: on | sfirstorder | hauto l: on | ].
    sinvert H1.
    split; intros.
    + sinvert H1.
      * econstructor;[sfirstorder | | sfirstorder]. eapply H8. { intro. assert (fv g2 y) by hauto l: on use:typing_fv_args. assert (fv g1 y) by hauto l: on use:ctx_subst_found_fv. sfirstorder. }
      * econstructor. eapply H6. { intro. assert (fv g1 y) by qauto l: on use:typing_fv_args. assert (fv g2 y) by hauto l: on use:ctx_subst_found_fv. sfirstorder. } sfirstorder. sfirstorder.
    + econstructor; sfirstorder.
  - sinvert H0.
    edestruct (H x y). best. best. best. best.
    split; intros.
    + sinvert H5.
      * econstructor. best. eapply H4. { intro. assert (fv g2 y) by hauto l: on use:typing_fv_args. assert (fv g1 y) by hauto l: on use:ctx_subst_found_fv. sfirstorder. }
      * econstructor. scongruence. hauto l: on.
Admitted.


Theorem typing_subst' : forall G G' e x y t i rs o,
  Typed o G rs e t i ->
  WFContext G ->
  ~ fv G x ->
  ~ bv_term e x ->
  ~ bv_term e y ->
  CtxSubst x y G G' ->
  Typed o G' rs (subst_var e x y) t i.
Proof.
best use:typing_subst.
Qed.