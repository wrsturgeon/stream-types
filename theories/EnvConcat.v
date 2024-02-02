From LambdaST Require Import
  Environment
  PrefixConcat.

Definition EnvConcat (n n' n'' : env) : Prop := forall x p p' p'',
  PrefixConcat p p' p'' ->
  n   x = Some p  ->
  n'  x = Some p' ->
  n'' x = Some p''. (* NOTE: says nothing about any `x` outside the intersecion of `n` and `n'`. *)
Arguments EnvConcat n n' n''/.
Hint Unfold EnvConcat : core.
