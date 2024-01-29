From LambdaST Require Import
  Ident
  Types
  Terms
  Prefix.
From Hammer Require Import
  Tactics.

(* TODO: fix with definintion. *)
Fixpoint sinkTm (p : prefix) : term := TmSink.