From Hammer Require Import Tactics.
From Coq Require Import String.
From LambdaST Require Import
  Terms
  FV
  Environment
  History
  Types.

(* [x/y]z *)
Definition subst_str (x y z : string) := if eqb z y then x else z.
Arguments subst_str x y/ z.
Hint Unfold subst_str : core.

(* TODO: the substitution for environments too! the terms with the built-in buffers need their vars swapped *)
(* subst_var e x y = e[x/y]. y goes away, x takes its place. *)
Fixpoint subst_var (e : term) (x : string) (y : string) : term :=
  match e with
  | TmSink
  | TmNil
  | TmUnit =>
      e
  | TmVar z =>
      TmVar (if eqb z y then x else z)
  | TmComma lhs rhs =>
      TmComma (subst_var lhs x y) (subst_var rhs x y)
  | TmSemic lhs rhs =>
      TmSemic (subst_var lhs x y) (subst_var rhs x y)
  | TmLet x' e e' =>
      TmLet x' (subst_var e x y) (subst_var e' x y)
  | TmLetPar lhs rhs bound body =>
      let subst_bound := subst_str x y bound in
      TmLetPar lhs rhs subst_bound (subst_var body x y)
  | TmLetCat t lhs rhs bound body =>
      let subst_bound := subst_str x y bound in
      (* let subst_body := if (eqb x lhs || eqb x rhs)%bool then body else subst_var body x y in *)
      TmLetCat t lhs rhs subst_bound (subst_var body x y)
  | TmInl e =>
      TmInl (subst_var e x y)
  | TmInr e =>
      TmInr (subst_var e x y)
  | TmPlusCase eta r z x' e1 y' e2 => TmPlusCase (env_subst_var x y eta) r (subst_str x y z) x' (subst_var e1 x y) y' (subst_var e2 x y)
  | TmCons lhs rhs =>
      TmCons (subst_var lhs x y) (subst_var rhs x y)
  | TmStarCase eta r s z e1 x' xs' e2 => TmStarCase (env_subst_var x y eta) r s (subst_str x y z) (subst_var e1 x y) x' xs' (subst_var e2 x y)
  | TmFix args hpargs g r e =>
      TmFix (subst_var_argsterm args x y) hpargs g r e
  | TmRec args hpargs =>
      TmRec (subst_var_argsterm args x y) hpargs
  | TmArgsLet args g e => TmArgsLet (subst_var_argsterm args x y) g e
  | TmHistPgm hp r' => TmHistPgm hp r'
  | TmWait eta r' s' z e => TmWait (env_subst_var x y eta) r' s' (subst_str x y z) (subst_var e x y)
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

Theorem bv_var_subst :
  (forall e, forall x y, bv_term e = bv_term (subst_var e x y)) /\
  (forall e, forall x y, bv_argsterm e = bv_argsterm (subst_var_argsterm e x y)).
Proof. apply term_mutual; cbn in *; intros; hauto lq: on. Qed.
