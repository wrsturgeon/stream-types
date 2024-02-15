From Hammer Require Import Tactics.
From Coq Require Import String.
From LambdaST Require Import
  Terms
  FV
  Types.

Definition subst_str (x y z : string) := if eqb z x then y else z.
Arguments subst_str x y/ z.
Hint Unfold subst_str : core.

(* subst_var e x y = e[x/y]. y goes away, x takes its place. *)
Fixpoint subst_var (e : term) (x : string) (y : string) : term :=
  match e with
  | TmSink
  | TmUnit =>
      e
  | TmVar z =>
      TmVar (if eqb z y then x else z)
  | TmComma lhs rhs =>
      TmComma (subst_var lhs x y) (subst_var rhs x y)
  | TmSemic lhs rhs =>
      TmSemic (subst_var lhs x y) (subst_var rhs x y)
  | TmLet x' e e' =>
      TmLet x' (if eqb y x' then e else subst_var e x y) (subst_var e' x y)
  | TmLetPar lhs rhs bound body =>
      let subst_bound := subst_str x y bound in
      let subst_body := if (eqb x lhs || eqb x rhs)%bool then body else subst_var body x y in
      TmLetPar lhs rhs subst_bound body
  | TmLetCat t lhs rhs bound body =>
      let subst_bound := subst_str x y bound in
      let subst_body := if (eqb x lhs || eqb x rhs)%bool then body else subst_var body x y in
      TmLetCat t lhs rhs subst_bound body
  | TmInl e =>
      TmInl (subst_var e x y)
  | TmInr e =>
      TmInr (subst_var e x y)
  | TmPlusCase eta r z x' e1 y' e2 =>
      TmPlusCase eta r z x' (subst_var e1 x y) y' (subst_var e2 x y)
  | TmFix args g r e =>
      TmFix (subst_var_argsterm args x y) g r e
  | TmRec args =>
      TmRec (subst_var_argsterm args x y)
  | TmArgsLet args g e => TmArgsLet (subst_var_argsterm args x y) g e
  end
with subst_var_argsterm (args : argsterm) (x : string) (y : string) :=
  match args with
  | ATmEmpty => ATmEmpty
  | ATmSng e => ATmSng (subst_var e x y)
  | ATmComma e1 e2 => ATmComma (subst_var_argsterm e1 x y) (subst_var_argsterm e2 x y)
  | ATmSemic1 e1 e2 => ATmSemic1 (subst_var_argsterm e1 x y) (subst_var_argsterm e2 x y)
  | ATmSemic2 e2 => ATmSemic2 (subst_var_argsterm e2 x y)
  end.
(* unfolding these is a nightmare
Arguments subst_var e x y.
Arguments subst_var_argsterm args x y.
*)

Lemma no_explosions_please : forall e x y x' e',
  subst_var (TmLet x' e e') x y =
  TmLet x' (if eqb y x' then e else subst_var e x y) (subst_var e' x y).
Proof. reflexivity. Qed.

(* NOTE: Had to add non-equality of x & y and make it a bi-implication *)
(* TODO: This still doesn't seem to work. Try `subst_var e x y = e <-> (x = y \/ ~fv e y)` *)
Theorem subst_not_fv :
  (forall e x y, subst_var e x y = e <-> (x = y \/ ~fv e y)) /\
  (forall args x y, subst_var_argsterm args x y = args <-> (x = y \/ ~fv args y)).
Proof.
(*
  apply term_mutual; intros.
  - hauto lq: on rew: off.
  - hauto lq: on rew: off.
  - split. { intro H'. apply eqb_neq in H'. cbn. rewrite H'. reflexivity. }
    intros H' C. cbn in *. subst. rewrite eqb_refl in H'. sinvert H'. apply H. reflexivity.
  - split. { hauto q: on. } hauto drew: off.
  - split. { hauto q: on. } hauto drew: off.
  - rewrite no_explosions_please. split.
    + intro Hfv. cbn in Hfv. apply Decidable.not_or in Hfv as [Hfv Hand].
      destruct (eqb_spec y bind); f_equal; [| sfirstorder | sfirstorder].
      subst. apply H0; [assumption |]. intro C. (* FUCK *) admit.
    + intros E C. cbn in C. destruct (eqb_spec y bind). 2: {
        assert (E1 : bound = subst_var bound x y) by congruence.
        assert (E2 : body = subst_var body x y) by congruence.
        apply H in E1; [| assumption]. apply H0 in E2; [| assumption].
        destruct C as [C | [C _]]; [apply E1 in C as [] | apply E2 in C as []]. }
      symmetry in e. subst. assert (E' : body = subst_var body x y) by congruence.
      apply H0 in E'; [| assumption]. destruct C as [C | [C _]]; [| apply E' in C as []].
      admit. (* okay, both cases are symmetrically wrong,
              * so there's probably something up with the theorem *)
*)
Admitted.
