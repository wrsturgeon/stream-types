From LambdaST Require Import
  Context
  History
  Terms
  Types
  Typing.

(* Definition B.37 *)
Variant rec_sig : Set :=
  | RecSigEmpty
  | RecSigRecur (H (* \Omega *) : hist_ctx) (G : context) (s : type (* TODO: flattened? *))
  .
(* Notation "H '|' G '->' s" := (RecSigRecur H G s) (at level 97, right associativity). *)
Hint Constructors rec_sig : core.

Definition B37 := rec_sig.
Arguments B37/.

Inductive tree (T : Type) :=
  | TreeEmpty
  | TreeComma (lhs rhs : tree T)
  | TreeSemic (lhs rhs : tree T)
  .
Arguments TreeEmpty {T}.
Arguments TreeComma {T} lhs rhs.
Arguments TreeSemic {T} lhs rhs.

(* Definition B.38 *)
Inductive RecursiveArgs (H : hist_ctx) : context -> tree term -> context -> Prop :=
  | RecArgsEmpty : forall G,
      RecursiveArgs H G TreeEmpty CtxEmpty
  (* TODO: What's the `s` on top of the line?
  | RecArgsHasTy : forall G e s x,
      RecursiveArgs H G e s ->
      RecursiveArgs H G e (CtxHasTy x s)
  *)
  | RecArgsSemic : forall G G' D D' e e',
      RecursiveArgs H G e D ->
      RecursiveArgs H G' e' D' ->
      RecursiveArgs H (CtxSemic G G') (TreeSemic e e') (CtxSemic D D')
  | RecArgsComma : forall G D D' e e',
      RecursiveArgs H G e D ->
      RecursiveArgs H G e' D' ->
      RecursiveArgs H G (TreeSemic e e') (CtxSemic D D')
  .
Arguments RecursiveArgs H G e D.
Hint Constructors RecursiveArgs : core.

Definition B38 := RecursiveArgs.
Arguments B38/.

(* TODO: B.43 *)
