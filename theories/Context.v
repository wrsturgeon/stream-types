From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Eqb
  FV
  Sets
  Terms
  Types.
From Coq Require Import
  List
  String.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : string) (ty : type)
  | CtxComma (g g': context)
  | CtxSemic (g g': context)
  .
Hint Constructors context : core.
Derive Show for context.
(* Derive Arbitrary for context. *)

Fixpoint fv_ctx ctx : set string :=
  match ctx with
  | CtxEmpty =>
      empty_set
  | CtxHasTy x _ =>
      singleton_set x
  | CtxComma lhs rhs
  | CtxSemic lhs rhs =>
      set_union (fv_ctx lhs) (fv_ctx rhs)
  end.

Instance fv_context : FV context := { fv := fv_ctx; }.

Fixpoint fv_ctx_li ctx :=
  match ctx with
  | CtxEmpty =>
      nil
  | CtxHasTy x _ =>
      cons x nil
  | CtxComma lhs rhs
  | CtxSemic lhs rhs =>
      List.app (fv_ctx_li lhs) (fv_ctx_li rhs)
  end.

Lemma reflect_fv_ctx : forall ctx x,
  Bool.reflect (fv ctx x) (lcontains x (fv_ctx_li ctx)).
Proof.
  induction ctx; cbn in *; intros.
  - constructor. intros [].
  - destruct (eqb_spec id x); constructor; assumption.
  - specialize (IHctx1 x). specialize (IHctx2 x). rewrite lcontains_app.
    sinvert IHctx1. { constructor. left. assumption. }
    sinvert IHctx2; constructor. { right. assumption. }
    intros [C | C]; tauto.
  - specialize (IHctx1 x). specialize (IHctx2 x). rewrite lcontains_app.
    sinvert IHctx1. { constructor. left. assumption. }
    sinvert IHctx2; constructor. { right. assumption. }
    intros [C | C]; tauto.
Qed.
Hint Resolve reflect_fv_ctx : core.

Fixpoint ctx_has x G : bool :=
  match G with
  | CtxEmpty =>
      false
  | CtxHasTy z _ =>
      if eqb x z then true else false
  | CtxComma lhs rhs
  | CtxSemic lhs rhs =>
      (ctx_has x lhs || ctx_has x rhs)%bool
  end.

Theorem reflect_ctx_has : forall G x,
  Bool.reflect (fv G x) (ctx_has x G).
Proof.
  induction G; cbn; intros.
  - constructor. intros [].
  - destruct (eqb_spec x id); constructor; symmetry; assumption.
  - specialize (IHG1 x). specialize (IHG2 x). sinvert IHG1. { constructor. left. assumption. }
    sinvert IHG2; constructor. { right. assumption. } intros [C | C]; tauto.
  - specialize (IHG1 x). specialize (IHG2 x). sinvert IHG1. { constructor. left. assumption. }
    sinvert IHG2; constructor. { right. assumption. } intros [C | C]; tauto.
Qed.

Fixpoint ctx_disj (arg_lhs arg_rhs : context) : bool :=
  match arg_lhs with
  | CtxEmpty =>
      true
  | CtxHasTy x _ =>
      negb (ctx_has x arg_rhs)
  | CtxComma lhs rhs
  | CtxSemic lhs rhs =>
      (ctx_disj lhs arg_rhs && ctx_disj rhs arg_rhs)%bool
  end.
Arguments ctx_disj lhs rhs : rename.

Theorem reflect_ctx_disj : forall lhs rhs,
  Bool.reflect (DisjointSets (fv lhs) (fv rhs)) (ctx_disj lhs rhs).
Proof.
  induction lhs; cbn; intros.
  - constructor. split; tauto.
  - cbn. destruct (reflect_ctx_has rhs id); constructor. { intro C. specialize (C id) as [C _]. tauto. }
    split; intros H C; subst; tauto.
  - specialize (IHlhs1 rhs). specialize (IHlhs2 rhs). sinvert IHlhs1. 2: { constructor. sfirstorder. }
    sinvert IHlhs2; constructor; sfirstorder.
  - specialize (IHlhs1 rhs). specialize (IHlhs2 rhs). sinvert IHlhs1. 2: { constructor. sfirstorder. }
    sinvert IHlhs2; constructor; sfirstorder.
Qed.

Fixpoint bindings ctx : set (prod string type) :=
  match ctx with
  | CtxEmpty =>
      empty_set
  | CtxHasTy x s =>
      singleton_set (pair x s)
  | CtxComma lhs rhs
  | CtxSemic lhs rhs =>
      set_union (bindings lhs) (bindings rhs)
  end.

Inductive WFContext : context -> Prop :=
  | WFCtxEmpty :
      WFContext CtxEmpty
  | WFCtxHasTy : forall x t,
      WFContext (CtxHasTy x t)
  | WFCtxComma : forall g g',
      WFContext g ->
      WFContext g' ->
      DisjointSets (fv g) (fv g') ->
      WFContext (CtxComma g g')
  | WFCtxSemic : forall g g',
      WFContext g ->
      WFContext g' ->
      DisjointSets (fv g) (fv g') ->
      WFContext (CtxSemic g g')
  .
Arguments WFContext G.
Hint Constructors WFContext : core.

Fixpoint wf_ctx (G : context) : bool :=
  match G with
  | CtxEmpty
  | CtxHasTy _ _ =>
      true
  | CtxComma lhs rhs
  | CtxSemic lhs rhs =>
      (wf_ctx lhs && wf_ctx rhs && ctx_disj lhs rhs)%bool
  end.

Theorem reflect_wf_ctx : forall G,
  Bool.reflect (WFContext G) (wf_ctx G).
Proof.
  induction G; cbn; repeat constructor;
  (sinvert IHG1; [| constructor; intro C; sinvert C; tauto]);
  (sinvert IHG2; [| constructor; intro C; sinvert C; tauto]);
  (destruct (reflect_ctx_disj G1 G2); constructor; [constructor; assumption |]);
  intro C; sinvert C; tauto.
Qed.

(* TODO: will need to prove that context derivatives preserve this... *)
