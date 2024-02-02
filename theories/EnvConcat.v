From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Derivative
  Environment
  FV
  Hole
  Inert
  Prefix
  PrefixConcat.

(* Definition B.25 (edited) *)
Definition EnvConcat (n n' n'' : env) : Prop := forall x p p' p'',
  PrefixConcat p p' p'' ->
  n   x = Some p  ->
  n'  x = Some p' ->
  n'' x = Some p''. (* NOTE: says nothing about any `x` outside the intersecion of `n` and `n'`. *)
Arguments EnvConcat n n' n''/.
Hint Unfold EnvConcat : core.

Definition env_cat (n n' : env) : env := fun x =>
  match n x with
  | None => None
  | Some nx =>
      match n' x with
      | None => None
      | Some n'x =>
          pfx_cat nx n'x
      end
  end.
Arguments env_cat n n'/ x.
Hint Unfold env_cat : core.

Theorem reflect_env_concat : forall n n',
  EnvConcat n n' (env_cat n n').
Proof.
  cbn. intros n n' x p p' p'' Hp E E'. rewrite E. rewrite E'.
  apply reflect_prefix_concat. assumption.
Qed.
Hint Resolve reflect_env_concat : core.

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
Hint Resolve env_concat_unique : core.

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
  forall n01x n12x z1x z2x,
  PrefixConcat nx n'x n01x ->
  PrefixConcat n01x n''x z1x ->
  PrefixConcat n'x n''x n12x ->
  PrefixConcat nx n12x z2x ->
  (z1 x = Some z1x /\ z2 x = Some z2x /\ z1x = z2x).
Proof.
  cbn. intros n n' n'' n01 n12 z1 z2 H01 Hz1 H12 Hz2 x nx n'x n''x E E' E'' n01x n12x z1x z2x P11 P12 P21 P22.
  specialize (H01 _ _ _ _ P11 E E'). specialize (H12 _ _ _ _ P21 E' E'').
  specialize (Hz1 _ _ _ _ P12 H01 E''). specialize (Hz2 _ _ _ _ P22 E H12).
  repeat split; [assumption | assumption |]. eapply pfx_cat_assoc_eq; [apply P11 | | |]; eassumption.
Qed.
Hint Resolve env_cat_assoc : core.

(* Theorem B.12 *)
Theorem env_subctx_bind_deriv : forall G D GD,
  Fill G D GD ->
  forall n G0,
  ContextDerivative n GD G0 ->
  exists G',
  forall D' D'' n',
  ContextDerivative n' D' D'' ->
  Agree Inert n n' (fv D) (fv D') ->
  forall nn' GD' G'D'',
  EnvConcat n n' nn' ->
  Fill G D' GD' ->
  Fill G' D'' G'D'' ->
  ContextDerivative nn' GD' G'D''.
  (* a behemoth *)
Proof.
  intros G D GD Hf n G0 Hd. generalize dependent G. generalize dependent D. induction Hd; intros.
  - sinvert Hf. eexists. intros D' D'' n' Hd Ha nn' GD' G'D'' Hc Hf' Hf''. sinvert Hf'. simpl (fv CtxEmpty) in Ha.
    (* TODO: this is really not going well *) Abort.
