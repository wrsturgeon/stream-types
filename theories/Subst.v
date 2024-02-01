From Coq Require Import String.
From LambdaST Require Import
  Terms
  Types.

Definition subst_str (x y z : string) := if eqb z x then y else z.
Arguments subst_str x y/ z.
Hint Unfold subst_str : core.

(* TODO: Joe, please tell me if this is what you had in mind; I guessed from the type signature *)
Fixpoint subst_var (e : term) (x : string) (y : string) : term :=
  match e with
  | TmSink
  | TmUnit =>
      e
  | TmVar z =>
      TmVar (subst_str x y z)
  | TmComma lhs rhs =>
      TmComma (subst_var lhs x y) (subst_var rhs x y)
  | TmSemic lhs rhs =>
      TmSemic (subst_var lhs x y) (subst_var rhs x y)
  | TmLet bind bound body =>
      let subst_bound := subst_var bound x y in
      let subst_body := if eqb bind x then (* shadowing *) body else (* no shadowing *) subst_var body x y in
      TmLet bind subst_bound subst_body
  | TmLetPar lhs rhs bound body =>
      let subst_bound := subst_str x y bound in
      let subst_body := if (eqb x lhs || eqb x rhs)%bool then body else subst_var body x y in
      TmLetPar lhs rhs subst_bound body
  | TmLetCat t lhs rhs bound body =>
      let subst_bound := subst_str x y bound in
      let subst_body := if (eqb x lhs || eqb x rhs)%bool then body else subst_var body x y in
      TmLetCat t lhs rhs subst_bound body
  end.
Arguments subst_var e/ x y.
