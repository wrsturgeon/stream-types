From QuickChick Require Import QuickChick.
From LambdaST Require Import
  FV
  Terms
  Types.
From Coq Require Import
  List
  String.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : string) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .
Hint Constructors context : core.
Derive Show for context.
Derive Arbitrary for context.

Fixpoint fv_ctx ctx : list string :=
  match ctx with
  | CtxEmpty => nil
  | CtxHasTy x _ => cons x nil
  | CtxComma lhs rhs | CtxSemic lhs rhs => fv_ctx lhs ++ fv_ctx rhs
  end.

Instance fv_context : FV context := { fv := fv_ctx; }.
