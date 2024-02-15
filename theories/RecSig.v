From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Hole
  Sets
  Subcontext
  Inert
  Types.

Inductive recsig : Set :=
  | NoRec : recsig
  | Rec : context -> type -> inertness -> recsig.
Hint Constructors recsig : core.

Definition jumpify rs :=
  match rs with
    NoRec => NoRec
  | Rec g s _ => Rec g s Jumpy
  end.