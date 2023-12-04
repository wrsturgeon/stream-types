From Coq Require Import
  Strings.String.

Definition ident : Set := string.

Bind Scope string_scope with ident.

Definition eq_id : ident -> ident -> bool := eqb.
Notation "a '=i' b" := (eq_id a b) (at level 98).
