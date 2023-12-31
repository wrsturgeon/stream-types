Declare Scope stream_type_scope.

Inductive type : Set :=
  | TyEps
  | TyOne
  | TyDot (lhs rhs : type)
  | TyPar (lhs rhs : type)
  | TySum (lhs rhs : type)
  | TyStar (starred : type)
  .

Bind Scope stream_type_scope with type.

Arguments TyDot lhs%stream_type_scope rhs%stream_type_scope.
Arguments TyPar lhs%stream_type_scope rhs%stream_type_scope.

Notation "'eps'" := TyEps : stream_type_scope.
Notation "'1'" := TyOne : stream_type_scope.
Notation "( lhs . rhs )" := (TyDot lhs rhs) : stream_type_scope.
Notation "( lhs || rhs )" := (TyPar lhs rhs) : stream_type_scope.
Notation "( lhs + rhs )" := (TySum lhs rhs) : stream_type_scope.
Notation "a *" := (TyStar a) (at level 1, left associativity) : stream_type_scope.
