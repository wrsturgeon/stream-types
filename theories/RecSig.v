From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Hole
  Sets
  Subcontext
  Inert
  History
  Types.

Inductive recsig : Set :=
  | NoRec : recsig
  | Rec : histctx -> context -> type -> inertness -> recsig.
Hint Constructors recsig : core.

Definition jumpify rs :=
  match rs with
    NoRec => NoRec
  | Rec o g s _ => Rec o g s Jumpy
  end.