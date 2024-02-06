From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Eqb
  FV
  Sets
  Types.
From Coq Require Import
  List
  String.

Fixpoint lcontains {T} `{Eqb T} x li :=
  match li with
  | nil => false
  | cons hd tl => (eqb hd x || lcontains x tl)%bool
  end.

Lemma lcontains_in : forall {T} `{Eqb T} x li,
  Bool.reflect (List.In x li) (lcontains x li).
Proof.
  intros. generalize dependent H. generalize dependent x.
  induction li; cbn in *; intros. { constructor. intros []. }
  destruct (eqb_spec a x). { constructor. left. assumption. }
  specialize (IHli x H). sinvert IHli; constructor. { right. assumption. }
  intros [C | C]; tauto.
Qed.
Hint Resolve lcontains_in : core.

Lemma lcontains_app : forall {T} a b `{Eqb T} x,
  lcontains x (a ++ b) = (lcontains x a || lcontains x b)%bool.
Proof.
  induction a; cbn in *; intros. { reflexivity. }
  destruct (eqb_spec a x); cbn. { reflexivity. } apply IHa.
Qed.
Hint Resolve lcontains_app : core.

Fixpoint lminus {T} `{Eqb T} x li :=
  match li with
  | nil => nil
  | cons hd tl => if eqb x hd then lminus x tl else cons hd (lminus x tl)
  end.

Lemma lminus_eq : forall {T} li `{Eqb T} x,
  lcontains x (lminus x li) = false.
Proof.
  induction li; cbn in *; intros. { reflexivity. }
  destruct (eqb_spec x a). { apply IHli. }
  cbn. destruct (eqb_spec a x). { subst. tauto. }
  rewrite IHli. reflexivity.
Qed.

Lemma lminus_neq : forall {T} li `{Eqb T} x y,
  x <> y ->
  lcontains x (lminus y li) = lcontains x li.
Proof.
  induction li; cbn in *; intros. { reflexivity. }
  destruct (eqb_spec a x). {
    subst. destruct (eqb_spec y x). { subst. tauto. } cbn. destruct (eqb_spec x x). { reflexivity. } tauto. }
  destruct (eqb_spec y a). { subst. rewrite IHli; [| assumption]. reflexivity. }
  cbn. destruct (eqb_spec a x). { subst. tauto. } rewrite IHli; [| assumption]. reflexivity.
Qed.

Fixpoint lsubset {T} `{Eqb T} small big :=
  match small with
  | nil => true
  | cons hd tl => (lcontains hd big && lsubset tl big)%bool
  end.

Lemma lsubset_incl : forall {T} `{Eqb T} small big,
  Bool.reflect (forall x, List.In x small -> List.In x big) (lsubset small big).
Proof.
  intros. generalize dependent H. generalize dependent big.
  induction small; cbn in *; intros. { constructor. intros _ []. }
  destruct (lcontains_in a big). 2: { constructor. intro C. apply n. apply C. left. reflexivity. }
  specialize (IHsmall big H). sinvert IHsmall; constructor; intros.
  - destruct H2; [subst | apply H1]; assumption.
  - intro C. apply H1. intros. apply C. right. assumption.
Qed.
Hint Resolve lsubset_incl : core.


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
