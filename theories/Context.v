From Coq Require Import
  List
  String.
From LambdaST Require Import
  Ident
  Terms
  Types
  ListUtil.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : ident) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .

Fixpoint vars_in ctx : list ident :=
  match ctx with
  | CtxEmpty => nil
  | CtxHasTy x _ => cons x nil
  | CtxComma lhs rhs | CtxSemic lhs rhs => vars_in lhs ++ vars_in rhs
  end.

Inductive wf_ctx : context -> Prop :=
| wf_CtxEmpty : wf_ctx CtxEmpty
| wf_CtxHasTy : forall x t, wf_ctx (CtxHasTy x t)
| wf_CtxComma : forall g g',
    wf_ctx g ->
    wf_ctx g' ->
    disjoint (vars_in g) (vars_in g') ->
    wf_ctx (CtxComma g g')
| wf_CtxSemic : forall g g',
    wf_ctx g ->
    wf_ctx g' ->
    disjoint (vars_in g) (vars_in g') ->
    wf_ctx (CtxSemic g g')
.

(* will need to prove that context derivatives preserve this... *)