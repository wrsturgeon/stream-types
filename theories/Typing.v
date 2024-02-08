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
  Types.


Inductive Typed : context -> term -> type -> inertness -> Prop :=
  | TParR : forall G e1 e2 s t i1 i2 i3,
      Typed G e1 s i1 ->
      Typed G e2 t i2 ->
      i_ub i1 i2 i3 ->
      Typed G (e1, e2) (TyPar s t) i3
  | TParL : forall G x y z s t e r Gxsyt Gzst i,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyPar s t)) Gzst ->
      Typed Gxsyt e r i ->
      Typed Gzst (TmLetPar x y z e) r i
  | TCatR : forall G D e1 e2 s t i1 i2 i3,
      Typed G e1 s i1 ->
      Typed D e2 t i2 ->
      inert_guard (i1 = Inert /\ ~(Nullable s)) i3 ->
      Typed (CtxSemic G D) (e1; e2) (TyDot s t) i3
  | TCatL : forall G x y z s t e r Gxsyt Gzst i,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyDot s t)) Gzst ->
      Typed Gxsyt e r i ->
      Typed Gzst (TmLetCat t x y z e) r i
  | TEpsR : forall G i,
      Typed G TmSink TyEps i
  | TOneR : forall G,
      Typed G TmUnit TyOne Jumpy
  | TVar : forall G x s Gxs i,
      Fill G (CtxHasTy x s) Gxs ->
      Typed Gxs (TmVar x) s i
  | TLet : forall G D Gxs x e e' s t GD i,
      ~fv G x ->
      Typed D e s Inert ->
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      Typed Gxs e' t i ->
      Typed GD (TmLet x e e') t i
  | TInl : forall G e s t i,
      Typed G e s i ->
      Typed G (TmInl e) (TySum s t) Jumpy
  | TInr : forall G e s t i,
      Typed G e s i ->
      Typed G (TmInr e) (TySum s t) Jumpy
  | TPlusCase : forall G x y z s t r Gz Gx Gy Gz' e1 e2 eta i i1 i2,
      ~ fv G x ->
      ~ fv G y ->
      Fill G (CtxHasTy z (TySum s t)) Gz ->
      Fill G (CtxHasTy x s) Gx ->
      Fill G (CtxHasTy y t) Gy ->
      EnvTyped eta Gz ->
      ContextDerivative eta Gz Gz' ->
      Typed Gx e1 r i1 ->
      Typed Gy e2 r i2 ->
      inert_guard (eta z = Some PfxSumEmp) i ->
      Typed Gz' (TmPlusCase eta r z x e1 y e2) r i
  | TSubCtx : forall G G' e s i,
      Subcontext G G' ->
      Typed G' e s i ->
      Typed G e s i
      
with ArgsTyped : context -> argsterm -> context -> Prop :=
  | T_ATmEmpty : forall g, ArgsTyped g ATmEmpty CtxEmpty
  | T_ATmSng : forall g e s x i,
      Typed g e s i ->
      ArgsTyped g (ATmSng e) (CtxHasTy x s)
  | T_ATmComma : forall g g1 g2 e1 e2,
      ArgsTyped g e1 g1 ->
      ArgsTyped g e2 g2 ->
      ArgsTyped g (ATmComma e1 e2) (CtxComma g1 g2)
  | T_ATmSemic : forall g1 g2 g1' g2' e1 e2,
      ArgsTyped g1 e1 g1' ->
      ArgsTyped g2 e2 g2' ->
      ArgsTyped (CtxSemic g1 g2) (ATmSemic e1 e2) (CtxSemic g1' g2')
.

Scheme Typed_ind' := Induction for Typed Sort Prop
with ArgsTyped_ind' := Induction for ArgsTyped Sort Prop.
Combined Scheme Typed_mutual from Typed_ind', ArgsTyped_ind'.

Hint Constructors Typed : core.
Hint Constructors ArgsTyped : core.

Check Typed_mutual.

Theorem typing_sub_inert : forall g e s i,
  Typed g e s i ->
  Typed g e s Jumpy
.
Proof.
intros.
induction H; intros.
- econstructor; sauto.
- econstructor; eauto.
- hfcrush.
- sfirstorder.
- hauto l: on.
- sauto lq: on.
- sfirstorder.
- best.
- best.
- best.
- destruct i; econstructor; eauto.
- best.
Qed.


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

Theorem typing_fv' : forall G e s i,
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
Admitted.

Theorem typing_fv : forall G e s i,
  Typed G e s i ->
  Subset (fv e) (fv G).
Proof.
(* trivial from prev *)
Admitted.

Hint Resolve typing_fv : core.

Theorem argstyping_fv : forall g e g',
  ArgsTyped g e g' ->
  forall x,
  fv e x ->
  fv g x.
Proof.
  intros.
  generalize dependent x.
  induction H; hauto l:on use:typing_fv'.
Qed.

(* TODO: will *)
Theorem sink_tm_typing : forall g p s s',
  PrefixTyped p s ->
  MaximalPrefix p ->
  Derivative p s s' ->
  Typed g (sink_tm p) s' Inert.
Proof.
Admitted.

Theorem typing_subst_nofv : forall e x g t i y,
  ~ fv e x ->
  Typed g e t i ->
  Typed g (subst_var e y x) t i.
Proof.
best use:subst_not_fv.
Qed.


(*

If G(x : s) |- e : t
then G(y : s) |- e[y/x] : t

*)

(* Todo: will. *)
Theorem typing_subst : forall h e x y s t i gx gy,
  Typed gx e t i ->
  WFContext gx ->
  ~ fv h y ->
  Fill h (CtxHasTy x s) gx ->
  Fill h (CtxHasTy y s) gy ->
  Typed gy (subst_var e y x) t i.
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
