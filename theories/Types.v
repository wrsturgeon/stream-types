From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import Eqb.

Inductive type : Set :=
  | TyEps
  | TyOne
  | TyDot (lhs rhs : type)
  | TyPar (lhs rhs : type)
  | TySum (lhs rhs : type)
  | TyStar (starred : type)
  .
Hint Constructors type : core.
Derive Show for type.
Derive Arbitrary for type.

Declare Scope stream_type_scope.
Bind Scope stream_type_scope with type.

Arguments TyDot lhs%stream_type_scope rhs%stream_type_scope.
Arguments TyPar lhs%stream_type_scope rhs%stream_type_scope.
Arguments TyStar starred%stream_type_scope.

Notation "'eps'" := TyEps : stream_type_scope.
Notation "'1'" := TyOne : stream_type_scope.
Notation "'(' lhs '.' rhs ')'" := (TyDot lhs rhs) : stream_type_scope.
Notation "'(' lhs '||' rhs ')'" := (TyPar lhs rhs) : stream_type_scope.
Notation "'(' lhs '+' rhs ')'" := (TySum lhs rhs) : stream_type_scope.
Notation "a '*'" := (TyStar a) (at level 1, left associativity) : stream_type_scope.

Scheme Equality for type.
Theorem eqb_spec_type : forall a b : type, Bool.reflect (a = b) (type_beq a b).
Proof.
  intros. destruct (type_beq a b) eqn:E; constructor;
  sfirstorder use: internal_type_dec_bl, internal_type_dec_lb.
Qed.
Instance eqb_type : Eqb type := { eqb := type_beq; eq_dec := type_eq_dec; eqb_spec := eqb_spec_type }.
Hint Unfold type_beq : core.
Hint Resolve type_eq_dec : core.
Hint Resolve eqb_spec_type : core.
