From Coq Require Import
  List
  String.
From LambdaST Require Import
  FV
  Ident
  Terms
  Types.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : ident) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .

Fixpoint fv_ctx (G : context) : set ident :=
  match G with
  | CtxEmpty => empty_set
  | CtxHasTy x _ => singleton_set x
  | CtxComma g g' | CtxSemic g g' => set_union (fv_ctx g) (fv_ctx g')
  end.

Instance fv_ctx_inst : FV context := { fv := fv_ctx }.

Inductive WFContext : context -> Prop :=
  | WFCtxEmpty :
      WFContext CtxEmpty
  | WFCtxHasTy : forall x t,
      WFContext (CtxHasTy x t)
  | WFCtxComma : forall g g',
      WFContext g ->
      WFContext g' ->
      Disjoint (fv g) (fv g') ->
      WFContext (CtxComma g g')
  | WFCtxSemic : forall g g',
      WFContext g ->
      WFContext g' ->
      Disjoint (fv g) (fv g') ->
      WFContext (CtxSemic g g')
  .

Inductive SubCtx : context -> context -> Prop := . (* TODO: Huh? *)

(* will need to prove that context derivatives preserve this... *)
