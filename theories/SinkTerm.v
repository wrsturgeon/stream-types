From Hammer Require Import Tactics.
From LambdaST Require Import
  Derivative
  Prefix
  PrefixConcat
  Terms.

(* Definition B.40 *)
Fixpoint sink_tm (p : prefix) : term :=
  match p with
  | PfxOneEmp => TmSink
  | PfxOneFull => TmSink
  | PfxEpsEmp => TmSink
  | PfxParPair p1 p2 => TmComma (sink_tm p1) (sink_tm p2)
  | PfxCatFst p1 => sink_tm p1
  | PfxCatBoth p1 p2 => sink_tm p2
  | PfxSumEmp => TmSink
  | PfxSumInl p => sink_tm p
  | PfxSumInr p => sink_tm p
  | PfxStarEmp => TmSink
  | PfxStarDone => TmSink
  | PfxStarFirst p1 => sink_tm p1
  | PfxStarRest p1 p2 => sink_tm p2
  end.

Definition B40 := sink_tm.
Arguments B40/.

(* Theorem B.41 *)
Theorem sink_tm_ty : forall p,
  MaximalPrefix p ->
  forall s,
  PrefixTyped p s ->
  forall s',
  Derivative p s s' ->
  False. (* TODO: What's the notation here? *)
Proof. Abort.

(*
Definition B41 := sink_tm_ty.
Arguments B41/.
*)

(* Theorem B.42 *)
Theorem sink_tm_cat : forall p p' p'',
  PrefixConcat p p' p'' ->
  sink_tm p' = sink_tm p''.
Proof. intros. induction H; cbn in *; scongruence. Qed.

Definition B42 := sink_tm_cat.
Arguments B42/.
