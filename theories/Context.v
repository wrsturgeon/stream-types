From QuickChick Require Import QuickChick.
From LambdaST Require Import
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

Fixpoint vars_in ctx : list string :=
  match ctx with
  | CtxEmpty => nil
  | CtxHasTy x _ => cons x nil
  | CtxComma lhs rhs | CtxSemic lhs rhs => vars_in lhs ++ vars_in rhs
  end.
