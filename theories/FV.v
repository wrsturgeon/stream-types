From Coq Require Import
  List
  String.

Class FV (T : Type) := { fv : T -> list (* TODO: set *) string }.
