From Coq Require Import String.
From LambdaST Require Import
  Context
  Prefix
  Types.

(* Definition B.32 *)
Inductive stlc_type : Set :=
  | STLCUnit
  | STLCProd (lhs rhs : stlc_type)
  | STLCSumT (lhs rhs : stlc_type)
  | STLCList (t : stlc_type)
  .
Hint Constructors stlc_type : core.

Definition B32 := stlc_type.
Arguments B32/.

(* Definition B.31 *)
Definition hist_ctx := string -> option stlc_type.
Hint Unfold hist_ctx : core.

Definition B31 := hist_ctx.
Arguments B31/.

(* TODO: propose using user-defined types like Coq's `Inductive` EVENTUALLY for e.g. here,
 * where type-level recursion corresponds to streamification (exactly how we use a list below),
 * since it would make these weird cases go away *)
Fixpoint flatten_type t :=
  match t with
  | TyOne
  | TyEps (* why not a void type? *) =>
      STLCUnit
  | TyDot lhs rhs
  | TyPar lhs rhs =>
      STLCProd (flatten_type lhs) (flatten_type rhs)
  | TySum lhs rhs =>
      STLCSumT (flatten_type lhs) (flatten_type rhs)
  | TyStar t =>
      STLCList (flatten_type t)
  end.

Fixpoint flatten_ctx (c : context) : hist_ctx :=
  match c with
  | CtxEmpty =>
      fun _ => None
  | CtxHasTy x t =>
      fun z => if eqb x z then Some (flatten_type t) else None
  | CtxComma lhs rhs
  | CtxSemic lhs rhs =>
      let lhs' := flatten_ctx lhs in
      let rhs' := flatten_ctx rhs in
      fun z => match rhs' z with None => lhs' z | Some t => Some t end
      (* NOTE: right precedence *)
  end.

(* TODO: or should this be a `Fixpoint`? *)
Inductive ToPrefix : type (* lambda-st type! *) -> stlc_type (* term? value? *) -> prefix -> Prop :=
  .
Hint Constructors ToPrefix : core.

(* TODO: Definition B.33 *)
