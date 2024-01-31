From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Sets
  FV
  Terms
  Types.
From Coq Require Import
  List
  String.
From LambdaST Require Import
  FV
  Terms
  Types.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : string) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .
Hint Constructors context : core.
Derive Show for context.
Derive Arbitrary for context.

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

(* TODO: will need to prove that context derivatives preserve this... *)

(* Argument order matches notation: (CtxLEq G G') === (G <= G') *)
Inductive CtxLEq (G G' : context) : Prop :=
  (* TODO *)
  .
Hint Constructors CtxLEq : core.
