From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  FV
  Hole
  Inert
  Nullable
  Sets
  Subcontext
  Terms
  Types.

Declare Scope typing_scope.


Inductive Typed : context -> term -> type -> Prop :=
  | TParR : forall G e1 e2 s t,
      Typed G e1 s ->
      Typed G e2 t ->
      Typed G (e1, e2) (TyPar s t)
  | TParL : forall G x y z s t e r Gxsyt Gzst,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyPar s t)) Gzst ->
      Typed Gxsyt e r ->
      Typed Gzst (TmLetPar x y z e) r
  | TCatR : forall G D e1 e2 s t,
      Typed G e1 s ->
      Typed D e2 t ->
      Typed (CtxSemic G D) (e1; e2) (TyDot s t)
  | TCatL : forall G x y z s t e r Gxsyt Gzst,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyDot s t)) Gzst ->
      Typed Gxsyt e r ->
      Typed Gzst (TmLetCat t x y z e) r
  | TEpsR : forall G,
      Typed G sink eps
  | TOneR : forall G,
      Typed G unit 1
  | TVar : forall G x s Gxs,
      Fill G (CtxHasTy x s) Gxs ->
      Typed Gxs (TmVar x) s
  | TSubCtx : forall G G' e s,
      Subcontext G G' ->
      Typed G' e s ->
      Typed G e s
  | TLet : forall G D x e e' s t Gxs GD,
      ~fv G x ->
      Typed D e s ->
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      Typed Gxs e' t ->
      Typed GD (TmLet x e e') t
  .
Hint Constructors Typed : core.

(* TODO:
Theorem typed_wf_term : forall G x T,
  G |- x \in T ->
  WFTerm (fv G) x.
*)

Theorem typing_fv : forall G e s,
    Typed G e s ->
    forall x,
    fv e x ->
    fv G x.
Proof.
  intros G e s Ht x Hfv. generalize dependent x. (* just for naming *)
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
  - sfirstorder use:subcontext_fv_subset.
  - eapply fv_fill. { eassumption. } cbn. destruct H' as [H' | [H' H'']]; [left | right]. { apply IHHt1. assumption. }
    specialize (IHHt2 _ H'). eapply fv_fill in IHHt2; [| eassumption].
    cbn in IHHt2. destruct IHHt2. { contradiction. } assumption.
Qed.
Hint Resolve typing_fv : core.



(* Inductive Inert : set (prod string type) -> term -> type -> Prop :=
  | InertParR : forall G e1 e2 s t,
      Inert G e1 s ->
      Inert G e2 t ->
      Inert G (e1 , e2) (TyPar s t)
  | InertParL : forall G x y z s t e r ,
      Inert (set_union G (set_union (singleton_set (pair x s)) (singleton_set (pair y t)))) e r ->
      Inert (set_union G (singleton_set (pair z (TyPar s t)))) (TmLetPar x y z e) r
  | InertCatR : forall G D e1 e2 s t,
      ~(Nullable s) ->
      DisjointSets G D ->
      Inert G e1 s ->
      Inert D e2 t ->
      Inert (set_union G D) (e1 ; e2) (TyDot s t)
  | InertCatL : forall G x y z s t e r ,
      Inert (set_union G (set_union (singleton_set (pair x s)) (singleton_set (pair y t)))) e r ->
      Inert (set_union G (singleton_set (pair z (TyDot s t)))) (TmLetCat t x y z e) r
  | InertEpsR : forall G,
      Inert G sink eps
  | InertVar : forall G x s,
      G (pair x s) ->
      Inert G (TmVar x) s
  | InertLet : forall G D x e e' s t,
      Inert D e s  ->
      Inert (set_union G (singleton_set (pair x s))) e' t ->
      Inert (set_union G D) (TmLet x e e') t
  | InertDrop : forall G x s t e ,
      Inert (set_minus G (singleton_set (pair x s))) e t ->
      Inert G (TmDrop x e) t
. *)
