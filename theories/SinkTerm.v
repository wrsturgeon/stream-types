From LambdaST Require Import
  Terms
  Prefix.

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
