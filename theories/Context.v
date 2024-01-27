From Coq Require Import
  List
  String.
From LambdaST Require Import
  Ident
  Terms
  Types.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : ident) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .
Hint Constructors context : core.

Fixpoint vars_in ctx : list ident :=
  match ctx with
  | CtxEmpty => nil
  | CtxHasTy x _ => cons x nil
  | CtxComma lhs rhs | CtxSemic lhs rhs => vars_in lhs ++ vars_in rhs
  end.
