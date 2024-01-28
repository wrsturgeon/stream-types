From LambdaST Require Import
  Sets.
From Coq Require Import
  String.

Class FV (T : Type) := { fv : T -> set string }.
