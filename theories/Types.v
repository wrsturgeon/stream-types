From QuickChick Require Import QuickChick.

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

Arguments TyDot lhs%stream_type_scope rhs%stream_type_scope.
Arguments TyPar lhs%stream_type_scope rhs%stream_type_scope.
Arguments TyStar starred%stream_type_scope.

Declare Scope stream_type_scope.
Bind Scope stream_type_scope with type.
Notation "'eps'" := TyEps : stream_type_scope.
Notation "'1'" := TyOne : stream_type_scope.
Notation "'(' lhs '.' rhs ')'" := (TyDot lhs rhs) : stream_type_scope.
Notation "'(' lhs '||' rhs ')'" := (TyPar lhs rhs) : stream_type_scope.
Notation "'(' lhs '+' rhs ')'" := (TySum lhs rhs) : stream_type_scope.
Notation "a '*'" := (TyStar a) (at level 1, left associativity) : stream_type_scope.
