From Coq Require Import String.
From LambdaST Require Import Sets.

Class FV (T : Type) := { fv : T -> set string }.
