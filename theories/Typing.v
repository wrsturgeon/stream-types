From Coq Require Import String.
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
  Types.

(* TODO:will pull in the rest of the rules (nil, cons, star-case)
   
  if done wiht that, wait (requires histctx)
*)
Inductive Typed : context -> recsig -> term -> type -> inertness -> Prop :=
  | TParR : forall G e1 e2 s t i1 i2 i3 rs,
      Typed G rs e1 s i1 ->
      Typed G rs e2 t i2 ->
      i_ub i1 i2 i3 ->
      Typed G rs (e1, e2) (TyPar s t) i3
  | TParL : forall G x y z s t e r Gxsyt Gzst i rs,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyPar s t)) Gzst ->
      Typed Gxsyt rs e r i ->
      Typed Gzst rs (TmLetPar x y z e) r i
  | TCatR : forall G D e1 e2 s t i1 i2 i3 rs,
      Typed G rs e1 s i1 ->
      Typed D rs e2 t i2 ->
      inert_guard (i1 = Inert /\ ~(Nullable s)) i3 ->
      Typed (CtxSemic G D) rs (e1; e2) (TyDot s t) i3
  | TCatL : forall G x y z s t e r Gxsyt Gzst i rs,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyDot s t)) Gzst ->
      Typed Gxsyt rs e r i ->
      Typed Gzst rs(TmLetCat t x y z e) r i
  | TEpsR : forall G i rs,
      Typed G rs TmSink TyEps i
  | TOneR : forall G rs,
      Typed G rs TmUnit TyOne Jumpy
  | TVar : forall G x s Gxs i rs,
      Fill G (CtxHasTy x s) Gxs ->
      Typed Gxs rs (TmVar x) s i
  | TLet : forall G D Gxs x e e' s t GD i rs,
      ~fv G x ->
      Typed D rs e s Inert ->
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      Typed Gxs rs e' t i ->
      Typed GD rs (TmLet x e e') t i
  | TInl : forall G e s t i rs,
      Typed G rs e s i ->
      Typed G rs (TmInl e) (TySum s t) Jumpy
  | TInr : forall G e s t i rs,
      Typed G rs e s i ->
      Typed G rs (TmInr e) (TySum s t) Jumpy
  | TPlusCase : forall G x y z s t r Gz Gx Gy Gz' e1 e2 eta i i1 i2 rs,
      ~ fv G x ->
      ~ fv G y ->
      Fill G (CtxHasTy z (TySum s t)) Gz ->
      Fill G (CtxHasTy x s) Gx ->
      Fill G (CtxHasTy y t) Gy ->
      EnvTyped eta Gz ->
      ContextDerivative eta Gz Gz' ->
      Typed Gx rs e1 r i1 ->
      Typed Gy rs e2 r i2 ->
      inert_guard (eta z = Some PfxSumEmp) i ->
      Typed Gz' rs (TmPlusCase eta r z x e1 y e2) r i
  | TRec : forall G G' s i args,
      ArgsTyped G' (Rec G s i) args G i ->
      Typed G' (Rec G s i) (TmRec args) s i
  | TFix : forall G G' rs args e r i,
      WFContext G ->
      ArgsTyped G' rs args G i ->
      Typed G (Rec G r i) e r i ->
      Typed G' rs (TmFix args G r e) r i
  | TmArgsLet : forall G G' args e rs s i,
      WFContext G ->
      ArgsTyped G' rs args G i ->
      Typed G rs e s i ->
      Typed G' rs (TmArgsLet args G e)  s i
  | TSubCtx : forall G G' e s i rs,
      Subcontext G G' ->
      Typed G' rs e s i ->
      Typed G rs e s i
      
with ArgsTyped : context -> recsig -> argsterm -> context -> inertness -> Prop :=
  | T_ATmEmpty : forall g rs i, ArgsTyped g rs ATmEmpty CtxEmpty i
  | T_ATmSng : forall g rs e s x i,
      Typed g rs e s i ->
      ArgsTyped g rs (ATmSng e) (CtxHasTy x s) i
  | T_ATmComma : forall g g1 g2 e1 e2 rs i1 i2 i3,
      ArgsTyped g rs e1 g1 i1 ->
      ArgsTyped g rs e2 g2 i2 ->
      i_ub i1 i2 i3 ->
      ArgsTyped g rs (ATmComma e1 e2) (CtxComma g1 g2) i3
  | T_ATmSemic1 : forall g1 g2 g1' g2' e1 e2 rs i1 i2 i3,
      ArgsTyped g1 rs e1 g1' i1 ->
      ArgsTyped g2 rs e2 g2' i2 ->
      inert_guard (i1 = Inert /\ ~(NullableCtx g1)) i3 ->
      ArgsTyped (CtxSemic g1 g2) rs (ATmSemic1 e1 e2) (CtxSemic g1' g2') i3
  | T_ATmSemic2 : forall g1 g2 g1' g2' e2 rs i,
      NullableCtx g1 ->
      ArgsTyped g2 rs e2 g2' i ->
      ArgsTyped (CtxSemic g1 g2) rs (ATmSemic2 e2) (CtxSemic g1' g2') i
.

Scheme Typed_ind' := Induction for Typed Sort Prop
with ArgsTyped_ind' := Induction for ArgsTyped Sort Prop.
Combined Scheme Typed_mutual from Typed_ind', ArgsTyped_ind'.

Hint Constructors Typed : core.
Hint Constructors ArgsTyped : core.

Check Typed_mutual.

Theorem typing_sub_inert : forall g e s i rs,
  Typed g rs e s i ->
  Typed g rs e s Jumpy
.
Proof.
  intros. induction H; cbn in *; intros.
  - econstructor; try eassumption; constructor.
  - econstructor; eassumption.
  - econstructor; try eassumption. cbn. intro C. discriminate C.
  - sfirstorder.
  - hauto l: on.
  - sauto lq: on.
  - sfirstorder.
  - best.
  - best.
  - best.
  - destruct i; econstructor; eauto.
Admitted.

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

Definition P_typing_fv (g : context) (rs : recsig) (e : term) (s : type) (i : inertness) :=
  forall x, fv e x -> fv g x.

Definition P_argstyping_fv (g : context) (rs : recsig) (args : argsterm) (g' : context) (i : inertness) :=
  forall x, fv args x -> fv g x.

Check Typed_mutual.

Theorem typing_fv' :
  (forall g rs e s i, Typed g rs e s i -> P_typing_fv g rs e s i) /\
  (forall g rs args g' i, ArgsTyped g rs args g' i -> P_argstyping_fv g rs args g' i).
Proof.
 apply Typed_mutual; intros; unfold P_typing_fv in *; unfold P_argstyping_fv in *.
 - sfirstorder.
 - admit.
 - sfirstorder.
 - admit.
 - sfirstorder.
 - sfirstorder.
 - hauto q: on use:fv_fill.
 - admit.
 - sfirstorder.
 - sfirstorder.
 - admit.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder.
 - sfirstorder use:subcontext_fv_subset.
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

Theorem typing_fv : forall G e s i rs,
  Typed G rs e s i ->
  Subset (fv e) (fv G).
Proof.
best use:typing_fv'.
Qed.

Theorem typing_fv_args : forall G G' e i rs,
  ArgsTyped G rs e G' i ->
  Subset (fv e) (fv G).
Proof.
best use:typing_fv'.
Qed.

Hint Resolve typing_fv : core.

(* TODO: will *)
Theorem sink_tm_typing : forall g p s s' rs,
  PrefixTyped p s ->
  MaximalPrefix p ->
  Derivative p s s' ->
  Typed g rs (sink_tm p) s' Inert.
Proof.
Admitted.

Theorem typing_subst_nofv : forall e x g t i y rs,
  ~ fv e x ->
  Typed g rs e t i ->
  Typed g rs (subst_var e y x) t i.
Proof.
  intros. assert (A : subst_var e y x = e); [| rewrite A; assumption].
  apply subst_not_fv. right. assumption.
Qed.

(*
If G(x : s) |- e : t
then G(y : s) |- e[y/x] : t
*)

(* Todo: will. *)
Theorem typing_subst : forall h e x y s t i gx gy rs,
  Typed gx rs e t i ->
  WFContext gx ->
  ~ fv h y ->
  Fill h (CtxHasTy x s) gx ->
  Fill h (CtxHasTy y s) gy ->
  Typed gy rs (subst_var e y x) t i.
Proof.
  intros.
  generalize dependent x.
  generalize dependent y.
  generalize dependent gy.
  generalize dependent h.
  generalize dependent s.
  induction H; intros.
  - admit.
  - admit.
  - assert (subst_var (TmSemic e1 e2) y x = TmSemic (subst_var e1 y x) (subst_var e2 y x)) by best.
    rewrite -> H6 in *.
    admit.
  - admit.
  - best.
  - best.
  - cbn in *. 
    destruct (string_dec x x0).
    + rewrite -> e. assert (eqb x0 x0 = true) by best use:eqb_refl. rewrite -> H4. 
      assert (h = G /\ s = s0) by best use:fill_reflect_var_localize.
      best.
    + admit.
Admitted.
