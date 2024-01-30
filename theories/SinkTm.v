From LambdaST Require Import
  Terms
  Prefix.

(* TODO: fix with definintion. *)
Definition sink_tm (p : prefix) : term := TmSink.
Arguments sink_tm/ p.
Hint Unfold sink_tm : core.
