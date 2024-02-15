From Coq Require Import String.
From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Eqb
  FV
  Context
  Sets
  Environment
  Types.

  (* #[export]Hint Unfold dep_ith : core. *)
Inductive term : Set :=
  | TmSink
  | TmUnit
  | TmVar (id : string)
  | TmComma (lhs rhs : term)
  | TmSemic (lhs rhs : term)
  | TmLet (bind : string) (bound body : term)
  | TmLetPar (lhs rhs bound : string) (body : term) (* Note that the bound term is NOT really a term, but we can w.l.o.g. surround it with another `let` *)
  | TmLetCat (t : type) (lhs rhs bound : string) (body : term)
  | TmInl (e : term)
  | TmInr (e : term)
  | TmPlusCase (eta : env) (r : type) (z : string) (x : string) (e1 : term) (y : string) (e2 : term)
  | TmFix (args : argsterm) (g : context) (r : type) (e : term)
  | TmRec (args : argsterm)
  | TmArgsLet (args : argsterm) (g : context) (e : term)
with
argsterm : Set :=
  | ATmEmpty
  | ATmSng (e : term)
  | ATmComma (e1 : argsterm) (e2 : argsterm)
  | ATmSemic1 (e1 : argsterm) (e2 : argsterm)
  | ATmSemic2 (e2 : argsterm)
.

Fixpoint fix_subst (g : context) (r : type) (e : term) (e' : term) :=
  match e' with
  | TmSink => TmSink
  | TmUnit => TmUnit
  | TmVar x => TmVar x
  | TmComma e1 e2 => TmComma (fix_subst g r e e1) (fix_subst g r e e2)
  | TmSemic e1 e2 => TmSemic (fix_subst g r e e1) (fix_subst g r e e2)
  | TmLet x e1 e2 => TmLet x (fix_subst g r e e1) (fix_subst g r e e2)
  | TmLetPar x y z e' => TmLetPar x y z (fix_subst g r e e')
  | TmLetCat t x y z e' => TmLetCat t x y z (fix_subst g r e e')
  | TmInl e' => TmInl (fix_subst g r e e')
  | TmInr e' => TmInr (fix_subst g r e e')
  | TmPlusCase eta r z x e1 y e2 => TmPlusCase eta r z x (fix_subst g r e e1) y (fix_subst g r e e2)
  | TmFix args g' r' e' => TmFix (fix_subst_args g r e args) g' r' e'
  | TmRec args => TmFix (fix_subst_args g r e args) g r e
  | TmArgsLet args g' e' => TmArgsLet (fix_subst_args g r e args) g' (fix_subst g r e e')
  
  end
with
fix_subst_args (g : context) (r : type) (e : term) (args : argsterm) := 
  match args with
  | ATmEmpty => ATmEmpty
  | ATmSng e' => ATmSng (fix_subst g r e e')
  | ATmComma e1 e2 => ATmComma (fix_subst_args g r e e1) (fix_subst_args g r e e2)
  | ATmSemic1 e1 e2 => ATmSemic1 (fix_subst_args g r e e1) (fix_subst_args g r e e2)
  | ATmSemic2 e2 => ATmSemic2 (fix_subst_args g r e e2)
  end
.

Scheme term_ind' := Induction for term Sort Prop
with argsterm_ind' := Induction for argsterm Sort Prop.
Combined Scheme term_mutual from term_ind', argsterm_ind'.


Hint Constructors term : core.

Declare Scope term_scope.
Bind Scope term_scope with term.
Notation "'sink'" := TmSink : term_scope.
Notation "'unit'" := TmUnit : term_scope.
(* Notation "`id`" := (TmVar id) : term_scope. *)
Notation "'(' lhs ',' rhs ')'" := (TmComma lhs rhs) : term_scope.
Notation "'(' lhs ';' rhs ')'" := (TmSemic lhs rhs) : term_scope.
Notation "'let' x '=' bound 'in' body" :=
  (TmLet x bound body) (at level 97, right associativity) : term_scope.
Notation "'let' '(' lhs ',' rhs ')' '=' both 'in' body" :=
  (TmLetPar lhs rhs both body) (at level 97, right associativity) : term_scope.
Notation "'let' '(' lhs ';' rhs ')' '=' both 'in' body" :=
  (TmLetCat lhs rhs both body) (at level 97, right associativity) : term_scope.

(* Scheme Equality for term.
Theorem eqb_spec_term : forall a b : term, Bool.reflect (a = b) (term_beq a b).
Proof.
  intros. destruct (term_beq a b) eqn:E; constructor;
  sfirstorder use: internal_term_dec_bl, internal_term_dec_lb.
Qed.
Instance eqb_term : Eqb term := { eqb := term_beq; eq_dec := term_eq_dec; eqb_spec := eqb_spec_term }.
Hint Unfold term_beq : core.
Hint Resolve term_eq_dec : core.
Hint Resolve eqb_spec_term : core.
 *)
Fixpoint fv_term e : set string :=
  match e with
  | TmSink | TmUnit => empty_set
  | TmVar x => singleton_set x
  | TmComma e1 e2 | TmSemic e1 e2 => set_union (fv_term e1) (fv_term e2)
  | TmLetPar x y z e | TmLetCat _ x y z e => set_union (singleton_set z) (
      set_minus (set_minus (fv_term e) (singleton_set x)) (singleton_set y))
  | TmLet x e e' => set_union (fv_term e) (set_minus (fv_term e') (singleton_set x))
  | TmInl e | TmInr e => fv_term e
  | TmPlusCase _ _ z x e1 y e2 => set_union (singleton_set z) (set_union (set_minus (fv_term e1) (singleton_set x)) (set_minus (fv_term e2) (singleton_set y)))
  | TmFix args _ _ _ => fv_argsterm args
  | TmRec args => fv_argsterm args
  | TmArgsLet args _ _ => fv_argsterm args
  end
with
fv_argsterm e : set string :=
  match e with
  | ATmEmpty => empty_set
  | ATmSng e => fv_term e
  | ATmComma e1 e2 | ATmSemic1 e1 e2 => set_union (fv_argsterm e1) (fv_argsterm e2)
  | ATmSemic2 e2 => fv_argsterm e2
  end.

Instance fv_term_inst : FV term := { fv := fv_term }.
Instance fv_argsterm_inst : FV argsterm := { fv := fv_argsterm }.

(*

term_ind
	 : 
argsterm_ind
	 : forall P : argsterm -> Prop,
       
       forall a : argsterm, P a

*)