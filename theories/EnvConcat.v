From Hammer Require Import Tactics.
From LambdaST Require Import
  Environment
  PrefixConcat.

(* Definition B.25 (edited) *)
Definition EnvConcat (n n' n'' : env) : Prop := forall x p p' p'',
  PrefixConcat p p' p'' ->
  n   x = Some p  ->
  n'  x = Some p' ->
  n'' x = Some p''. (* NOTE: says nothing about any `x` outside the intersecion of `n` and `n'`. *)
Arguments EnvConcat n n' n''/.
Hint Unfold EnvConcat : core.

(* Theorem B.26, part I *)
Theorem env_concat_unique : forall n n' n1,
  EnvConcat n n' n1 ->
  forall n2,
  EnvConcat n n' n2 ->
  forall x nx n'x n''x,
  n x = Some nx ->
  n' x = Some n'x ->
  PrefixConcat nx n'x n''x ->
  n1 x = n2 x.
Proof. hauto q: on. Qed.

(* Theorem B.26 part II is trivial: environment concatenation is universal in the revised definition *)

(* skipping B.27-29, since I'm not sure what changed with the definition *)

(* Theorem B.30 *)
Theorem env_cat_assoc : forall n n' n'' n01 n12 z1 z2,
  EnvConcat n n' n01 ->
  EnvConcat n01 n'' z1 ->
  EnvConcat n' n'' n12 ->
  EnvConcat n n12 z2 ->
  forall x nx n'x n''x,
  n x = Some nx ->
  n' x = Some n'x ->
  n'' x = Some n''x ->
  z1 x = z2 x.
Proof.
  cbn. intros n n' n'' n01 n12 z1 z2 H1 H2 H3 H4 x nx n'x n''x E E' E''.
  specialize (H1 x). specialize (H2 x). specialize (H3 x). specialize (H4 x).
  (* TODO: GOD THIS IS A PAIN IN THE ASS *) Abort.
