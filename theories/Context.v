From Coq Require Import
  List
  String.
From LambdaST Require Import
  Ident
  Terms
  Types
  FV.


Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : ident) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .

Fixpoint context_fv (G : context) : set ident :=
  match G with
  | CtxEmpty => FV.empty
  | CtxHasTy x _ => FV.singleton x
  | CtxComma g g' | CtxSemic g g' => FV.union (context_fv g) (context_fv g')
  end
  .


Instance context_fv_inst : FV context :=
{
  fv := context_fv
}.

Inductive wf_ctx : context -> Prop :=
| wf_CtxEmpty : wf_ctx CtxEmpty
| wf_CtxHasTy : forall x t, wf_ctx (CtxHasTy x t)
| wf_CtxComma : forall g g',
    wf_ctx g ->
    wf_ctx g' ->
    disjoint (fv g) (fv g') ->
    wf_ctx (CtxComma g g')
| wf_CtxSemic : forall g g',
    wf_ctx g ->
    wf_ctx g' ->
    disjoint (fv g) (fv g') ->
    wf_ctx (CtxSemic g g')
.

Inductive sub_ctx : context -> context -> Prop := .

(* will need to prove that context derivatives preserve this... *)