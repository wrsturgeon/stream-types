From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Sets
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

Fixpoint vars_in ctx : set string :=
  match ctx with
  | CtxEmpty => empty_set
  | CtxHasTy x _ => singleton_set x
  | CtxComma lhs rhs | CtxSemic lhs rhs => set_union (vars_in lhs) (vars_in rhs)
  end.
