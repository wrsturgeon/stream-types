From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Sets
  FV
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
Hint Constructors WFContext : core.

Inductive CtxSubst (x : string) (y : string) : context -> context -> Prop :=
| CSSng : forall s, CtxSubst x y (CtxHasTy y s) (CtxHasTy x s)
| CSComma1 : forall g g' d,
    CtxSubst x y g g' ->
    CtxSubst x y (CtxComma g d) (CtxComma g' d)
| CSComma2 : forall g g' d,
    CtxSubst x y g g' ->
    CtxSubst x y (CtxComma d g) (CtxComma d g')
| CSSemic1 : forall g g' d,
    CtxSubst x y g g' ->
    CtxSubst x y (CtxSemic g d) (CtxSemic g' d)
| CSSemic2 : forall g g' d,
    CtxSubst x y g g' ->
    CtxSubst x y (CtxSemic d g) (CtxSemic d g').

Theorem ctx_subst_exists : forall x y g, fv g y -> exists g', CtxSubst x y g g'.
Proof.
intros.
generalize dependent x. generalize dependent y.
induction g; intros.
- best.
- sauto lq: on.
- sauto q: on.
- sauto q: on.
Qed.

Theorem ctx_subst_not_exists : forall y g,
  ~fv g y ->
  (forall x g', ~CtxSubst x y g g').
Proof.
intros y g. generalize dependent y.
induction g; sauto lq: on.
Qed.

Theorem ctx_subst_found_fv : forall x y g g',
  CtxSubst x y g g' ->
  fv g y.
Proof.
  intros.
  induction H; hauto lq: on.
Qed.

Theorem ctx_subst_det : forall x y g g' g'',
  WFContext g ->
  CtxSubst x y g g' ->
  CtxSubst x y g g'' ->
  g' = g''.
Proof.
  intros.
  generalize dependent g''.
  generalize dependent H.
  induction H0; intros H; sinvert H; intros.
  - best.
  - sinvert H1;[sfirstorder|].
    assert (fv g y) by sfirstorder use:ctx_subst_found_fv.
    assert (~fv d y) by sfirstorder.
    hauto q: on use:ctx_subst_not_exists.
  - sinvert H1;[|sfirstorder].
    assert (fv g y) by sfirstorder use:ctx_subst_found_fv.
    assert (~fv d y) by sfirstorder.
    hauto q: on use:ctx_subst_not_exists.
  - sinvert H1;[sfirstorder|].
    assert (fv g y) by sfirstorder use:ctx_subst_found_fv.
    assert (~fv d y) by sfirstorder.
    hauto q: on use:ctx_subst_not_exists.
  - sinvert H1;[|sfirstorder].
    assert (fv g y) by sfirstorder use:ctx_subst_found_fv.
    assert (~fv d y) by sfirstorder.
    hauto q: on use:ctx_subst_not_exists.
Qed.

Theorem ctx_subst_found_fv' : forall x y g g',
  CtxSubst x y g g' ->
  fv g' x.
Proof.
  intros.
  induction H; hauto lq: on.
Qed.

Theorem ctx_subst_no_found_fv : forall z g' g x y,
  CtxSubst x y g g' ->
  ~fv g z ->
  z <> x ->
  ~fv g' z.
Proof.
intros. generalize dependent z.
induction H;sfirstorder.
Qed.

Theorem ctx_subst_fv : forall x y g g',
  CtxSubst x y g g' ->
  WFContext g ->
  SetEq (fv g') (set_union (set_minus (fv g) (singleton_set y)) (singleton_set x)).
Proof.
  intros.
  generalize dependent H0.
  induction H; intros; [sfirstorder | | | | ]; sinvert H0; assert (fv g y) by sfirstorder use:ctx_subst_found_fv; assert (~fv d y) by sfirstorder; hauto q: on.
Qed.


Theorem ctx_subst_wf : forall x y g g',
  WFContext g ->
  CtxSubst x y g g' ->
  ~ fv g x ->
  WFContext g'.
Proof.
  intros.
  generalize dependent H.
  generalize dependent H1.
  induction H0; intros; [ sauto lq: on | | | | ]; sauto q: on use:ctx_subst_fv.
Qed.

