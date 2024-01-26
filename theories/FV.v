From LambdaST Require Import
  Ident.

Definition set A := A -> Prop.

Definition empty_set {A} : set A :=
  fun _ => False.
Arguments empty_set {A}/ x.

Definition singleton_set {A} (e : A) : set A :=
  fun x => e = x.
Arguments singleton_set {A} e/ x.

Definition set_union {A} (X Y : set A) : set A :=
  fun x => X x \/ Y x.
Arguments set_union {A} X Y/ x.

Definition set_intersection {A} (X Y : set A) : set A :=
  fun x => X x /\ Y x.
Arguments set_intersection {A} X Y/ x.

Definition set_minus {A} (X Y : set A) : set A :=
  fun x => X x /\ ~(Y x).
Arguments set_minus {A} X Y/ x.

Definition Disjoint {A} (X Y : set A) : Prop :=
  (forall x, X x -> ~(Y x)) /\ (forall x, Y x -> ~(X x)).
Arguments Disjoint {A} X Y/.

(* Meant to be read with *currying* in mind: `Contains a b` = `(Contains a) b`, i.e. "b contains a" *)
Definition Contains {T} (a b : set T) : Prop := forall x, a x -> b x.
Arguments Contains/ {T} a b.

Definition SetEq {T} (a b : set T) : Prop := forall x, a x <-> b x.
Arguments SetEq/ {T} a b.

Class FV (A : Type) := { fv : A -> set ident }.
