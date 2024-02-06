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
(* TODO: Joe, please tell me if this is what you had in mind; I guessed from the type signature *)
Fixpoint subst_var (e : term) (x : string) (y : string) : term :=
  match e with
  | TmSink
  | TmUnit =>
      e
  | TmVar z =>
      TmVar (if eqb z y then x else z)
  | TmComma lhs rhs => TmComma (subst_var lhs x y) (subst_var rhs x y)
  | TmSemic lhs rhs => TmSemic (subst_var lhs x y) (subst_var rhs x y)
  | TmLet x' e e' => TmLet x' (if eqb y x' then e else subst_var e x y) (subst_var e' x y)
      (* let subst_bound := subst_var bound x y in *)
      (* let subst_body := if eqb bind x then shadowing body else no shadowing subst_var body x y in *)
      (* TmLet bind subst_bound subst_body *)
  | TmLetPar lhs rhs bound body =>
      let subst_bound := subst_str x y bound in
      let subst_body := if (eqb x lhs || eqb x rhs)%bool then body else subst_var body x y in
      TmLetPar lhs rhs subst_bound body
  | TmLetCat t lhs rhs bound body =>
      let subst_bound := subst_str x y bound in
      let subst_body := if (eqb x lhs || eqb x rhs)%bool then body else subst_var body x y in
      TmLetCat t lhs rhs subst_bound body
  | TmInl e => TmInl (subst_var e x y)
  | TmInr e => TmInr (subst_var e x y)
  | TmPlusCase eta r z x' e1 y' e2 => TmPlusCase eta r z x' (subst_var e1 x y) y' (subst_var e2 x y)
  | TmFix args g r e => TmFix (subst_var_argsterm args x y) g r e
  | TmRec args => TmRec (subst_var_argsterm args x y)
  end
with
subst_var_argsterm (args : argsterm) (x : string) (y : string) :=
    match args with
    | ATmEmpty => ATmEmpty
    | ATmSng e => ATmSng (subst_var e x y)
    | ATmComma e1 e2 => ATmComma (subst_var_argsterm e1 x y) (subst_var_argsterm e2 x y)
    | ATmSemic e1 e2 => ATmSemic (subst_var_argsterm e1 x y) (subst_var_argsterm e2 x y)
    end
.

Arguments subst_var e/ x y.

(* TODO: will. *)
Theorem subst_not_fv : 
    (forall e, forall x y, ~(fv e y) -> e = subst_var e x y)
    /\
    (forall args, forall x y, ~(fv args y) -> args = subst_var_argsterm args x y).
Proof.
apply term_mutual; intros.
- hauto lq: on rew: off.
- hauto lq: on rew: off.
- admit.
- qauto l: on.
- hauto lq: on rew: off.
- assert (subst_var (TmLet bind bound body) x y = TmLet bind (if eqb bind y then bound else subst_var bound x y) (subst_var body x y)) by best.
  rewrite -> H2.
  cbn in H1.
  assert (~ fv bound y) by best.
  assert (~ (fv body y /\ bind <> y)) by best.
  assert ((~ fv body y) \/ bind = y) by admit.
  destruct H5.
  + best.
  + rewrite -> H5. admit.
Admitted.