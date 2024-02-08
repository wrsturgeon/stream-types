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
