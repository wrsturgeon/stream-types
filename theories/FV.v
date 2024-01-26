From LambdaST Require Import
  Ident.

Definition set A := A -> Prop.

Definition empty {A : Type} : set A := fun _ => False.

Definition singleton {A : Type} (x : A) : set A :=
    fun y => x = y.

Definition union {A : Type} (X Y : set A) : set A :=
    fun x => X x \/ Y x.

Definition intersection {A : Type} (X Y : set A) : set A :=
    fun x => X x /\ Y x.

Definition minus {A : Type} (X Y : set A) : set A :=
    fun x => X x /\ ~(Y x).

Definition disjoint {A : Type} (X Y : set A) : Prop :=
    (forall x, X x -> ~(Y x)) /\ (forall x, Y x -> ~(X x)).

Class FV (A : Type) :=
  { fv : A -> set ident }.

