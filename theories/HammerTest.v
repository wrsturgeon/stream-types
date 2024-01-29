From Hammer Require Import Hammer.

Example modus_ponens : forall P Q,
  P ->
  (P -> Q) ->
  Q.
Proof.
  hammer.
Qed.
