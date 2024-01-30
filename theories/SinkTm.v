From LambdaST Require Import
  Ident
  Types
  Terms
  Prefix.
From Hammer Require Import
  Tactics.

(* TODO: fix with definintion. *)
Fixpoint sinkTm (p : prefix) : term :=
    match p with
        PfxOneEmp => TmSink
      | PfxOneFull => TmSink
      | PfxEpsEmp => TmSink
      | PfxParPair p1 p2 => TmComma (sinkTm p1) (sinkTm p2)
      | PfxCatFst p1 => sinkTm p1
      | PfxCatBoth p1 p2 => sinkTm p2
      | PfxSumEmp => TmSink
      | PfxSumInl p => sinkTm p
      | PfxSumInr p => sinkTm p
      | PfxStarEmp => TmSink
      | PfxStarDone => TmSink
      | PfxStarFirst p1 => sinkTm p1
      | PfxStarRest p1 p2 => sinkTm p2
    end
.

Theorem sink_reactive : forall p, reactive (sinkTm p).
Proof.
induction p; sauto lq: on.
Qed.