From Coq Require Import
  Program.Equality
  List
  (* String. *)
.
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
      Typed o G rs (e1, e2) (TyPar s t) i3
  | TParL : forall G x y z s t e r Gxsyt Gzst i rs o,
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
      Typed o (CtxSemic G D) rs (e1; e2) (TyDot s t) i3
  | TCatL : forall G x y z s t e r Gxsyt Gzst i rs o,
      x <> z -> 
      y <> z -> 
      x <> y ->
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
      ~ fv G x ->
      ~ fv G y ->
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
  | TWait : forall o G Gx Gx' Gemp z s r i i' e rs eta,
      Fill G (CtxHasTy z s) Gx ->
      EnvTyped eta Gx ->
      ContextDerivative eta Gx Gx' ->
      Fill G CtxEmpty Gemp ->
      Typed (cons (flatten_type s) o) Gemp rs e r i ->
      inert_guard ((forall p, eta z = Some p -> ~ MaximalPrefix p) /\ ~Nullable s) i' ->
      Typed o Gx' rs (TmWait eta r s z e) r i'
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
  - hauto l: on.
  - sfirstorder.
  - sfirstorder.
  - sfirstorder.
  - hauto l: on.
  - hauto l: on.
  - hauto l: on.
  - hauto l: on.
  - hauto l: on.
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


(* Theorem typing_sub_inert_mut :
  (forall g rs e s i, Typed g rs e s i -> Typed g (jumpify rs) e s Jumpy)
  /\
  (forall g rs e g' i, ArgsTyped g rs e g' i -> ArgsTyped g (jumpify rs) e g' Jumpy)
.
Proof.
  apply Typed_mutual; intros.
  - ecrush.
  - sfirstorder.
  - sblast.
  - sfirstorder.
  - hauto l: on.
  - sauto lq: on.
  - sfirstorder.
  - econstructor. eauto. 
  - sfirstorder.
  - best.
  - econstructor; eauto. scongruence.
  - eapply TRec.
Admitted. *)

(* TODO:
Theorem typed_wf_term : forall G x T,
  G |- x \in T ->
  WFTerm (fv G) x.
*)

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
 - admit. (* last remaining case *)
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
Admitted.

(* Theorem typing_fv' : forall G e s i,
  Typed G e s i ->
  forall x,
  fv e x ->
  fv G x.
Proof.
  intros G e s i Ht x Hfv. generalize dependent x. (* just for naming *)
  induction Ht; try rename x into x' (* hands off my `x`! *); intros x H'; cbn in *.
  - destruct H'; [apply IHHt1 | apply IHHt2]; assumption.
  - eapply fv_fill. { eassumption. } cbn. destruct H' as [| [[H2' H3'] H4]]; [left | right]. { assumption. }
    specialize (IHHt _ H2'). eapply fv_fill in IHHt; [| eassumption].
    cbn in IHHt. destruct IHHt; [| assumption]. destruct H5; contradiction H5.
  - destruct H'; [left; apply IHHt1 | right; apply IHHt2]; assumption.
  - eapply fv_fill. { eassumption. } cbn. destruct H' as [| [[H2' H3'] H4]]; [left | right]. { assumption. }
    specialize (IHHt _ H2'). eapply fv_fill in IHHt; [| eassumption].
    cbn in IHHt. destruct IHHt; [| assumption]. destruct H5; contradiction H5.
  - destruct H' as [].
  - destruct H' as [].
  - eapply fv_fill. { eassumption. } cbn. left. assumption.
  - (*eapply subcontext_fv_subset; [| apply IHHt]; eassumption.*) admit.
  - admit.
  (* - eapply fv_fill. { eassumption. } cbn. destruct H' as [H' | [H' H'']]; [left | right]. { apply IHHt1. assumption. }
    specialize (IHHt2 _ H'). eapply fv_fill in IHHt2; [| eassumption].
    cbn in IHHt2. destruct IHHt2. { contradiction. } assumption. *)
  - apply IHHt. assumption.
  - (*apply IHHt. assumption. *) admit.
  - admit. (*apply fv_context_derivative in H5. apply H5. clear Gz' H5. eapply fv_fill; [eassumption |]. cbn.
    destruct H'. { left. assumption. } destruct H5 as [[Hfv Hx'x] | [Hfv Hyx]]. {
      apply IHHt1 in Hfv. eapply fv_fill in Hfv; [| eassumption]. destruct Hfv. { tauto. } right. assumption. }
    apply IHHt2 in Hfv. eapply fv_fill in Hfv; [| eassumption]. destruct Hfv. { tauto. } right. assumption.*)
Admitted. *)



(* Theorem argstyping_fv' : forall g e g',
  ArgsTyped g e g' ->
  forall x,
  fv e x ->
  fv g x.
Proof.
  intros.
  generalize dependent x.
  induction H; hauto l:on use:typing_fv'.
Qed. *)

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


(* Todo: will: PRIORITY. *)
Theorem typing_subst : forall h e x y s t i gx gy rs o,
  Typed o gx rs e t i ->
  WFContext gx ->
  ~ fv h y ->
  Fill h (CtxHasTy x s) gx ->
  Fill h (CtxHasTy y s) gy ->
  Typed o gy rs (subst_var e y x) t i.
Proof.
  intros h e x y s t i gx gy rs o Ht Hw Hn Hx Hy.
  generalize dependent gy.
  generalize dependent s.
  generalize dependent y.
  generalize dependent x.
  generalize dependent h.
  generalize dependent Hw.
  induction Ht; cbn in *; intros.
  - econstructor; [eapply IHHt1 | eapply IHHt2 |]; eassumption.
  - econstructor; try eassumption. assert (HwG := wf_ctx_hole _ Hw _ _ H3).
    assert (Hwfc : WFContext (CtxComma (CtxHasTy x s) (CtxHasTy y t))). {
      repeat constructor; intros Hf C; cbn in *; subst; apply H; reflexivity. }
    assert (Hd : DisjointSets (fv G) (fv (CtxComma (CtxHasTy x s) (CtxHasTy y t)))). {
      constructor; [intros Hf [] | intros [] Hf]; cbn in *; subst; contradiction Hf. }
    eassert (HwGxsyt := wf_ctx_fill _ _ _ H2 HwG Hwfc Hd).
    Search gy. admit.
  - assert (subst_var (TmSemic e1 e2) y x = TmSemic (subst_var e1 y x) (subst_var e2 y x)) by best.
    admit.
  - admit.
  - best.
  - best.
  - admit.
  - admit.
Admitted.

Theorem typing_histval_subst : 
  (forall o g rs e s i, Typed o g rs e s i -> forall ts t ts' v n, o = app ts (cons t ts') -> length ts = n -> HistValTyped v t -> Typed (app ts ts') g rs (histval_subst v n e) s i) /\ 
  (forall o g rs args g' i, ArgsTyped o g rs args g' i -> forall ts t ts' v n, o = app ts (cons t ts') -> length ts = n -> HistValTyped v t -> ArgsTyped (app ts ts') g rs (histval_subst_args v n args) g' i).
Proof.
  apply Typed_mutual; intros.
  - cbn. econstructor. eauto. eauto. sfirstorder.
  - hauto drew: off.
  - sblast.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
  - hauto drew: off.
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