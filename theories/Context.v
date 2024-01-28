From Coq Require Import
  List
  String.
From LambdaST Require Import
  Ident
  Sets
  Terms
  Types.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : ident) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .
Hint Constructors context : core.

Fixpoint vars_in ctx : set ident :=
  match ctx with
  | CtxEmpty => empty_set
  | CtxHasTy x _ => singleton_set x
  | CtxComma lhs rhs | CtxSemic lhs rhs => set_union (vars_in lhs) (vars_in rhs)
  end.
