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
with
argsterm : Set :=
  | ATmEmpty
  | ATmSng (e : term)
  | ATmComma (e1 : argsterm) (e2 : argsterm)
  | ATmSemic (e1 : argsterm) (e2 : argsterm)
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
  end
with
fix_subst_args (g : context) (r : type) (e : term) (args : argsterm) := 
  match args with
  | ATmEmpty => ATmEmpty
  | ATmSng e' => ATmSng (fix_subst g r e e')
  | ATmComma e1 e2 => ATmComma (fix_subst_args g r e e1) (fix_subst_args g r e e2)
  | ATmSemic e1 e2 => ATmSemic (fix_subst_args g r e e1) (fix_subst_args g r e e2)
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
Notation "'let' x ':' t '=' bound 'in' body" :=
  (TmLet t x bound body) (at level 97, right associativity) : term_scope.
Notation "'let' '(' lhs ',' rhs ')' '=' both 'in' body" :=
  (TmLetPar lhs rhs both body) (at level 97, right associativity) : term_scope.
Notation "'let' t '(' lhs ';' rhs ')' '=' both 'in' body" :=
  (TmLetCat t lhs rhs both body) (at level 97, right associativity) : term_scope.

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
  end
with
fv_argsterm e : set string :=
  match e with
  | ATmEmpty => empty_set
  | ATmSng e => fv_term e
  | ATmComma e1 e2 | ATmSemic e1 e2 => set_union (fv_argsterm e1) (fv_argsterm e2)
  end.

Instance fv_term_inst : FV term := { fv := fv_term }.
Instance fv_argsterm_inst : FV argsterm := { fv := fv_argsterm }.

Fixpoint fv_term_li e :=
  match e with
  | TmSink | TmUnit => nil
  | TmVar x => cons x nil
  | TmComma e1 e2 | TmSemic e1 e2 => List.app (fv_term_li e1) (fv_term_li e2)
  | TmLetPar x y z e | TmLetCat _ x y z e => cons z (lminus y (lminus x (fv_term_li e)))
  | TmLet _ x e e' => List.app (fv_term_li e) (lminus x (fv_term_li e'))
  end.

Lemma reflect_fv_term : forall t x,
  Bool.reflect (fv t x) (lcontains x (fv_term_li t)).
Proof.
  induction t; cbn in *; intros.
  - constructor. intros [].
  - constructor. intros [].
  - destruct (String.eqb_spec id x); constructor; assumption.
  - specialize (IHt1 x). specialize (IHt2 x). rewrite lcontains_app.
    sinvert IHt1. { constructor. left. assumption. }
    sinvert IHt2; constructor. { right. assumption. }
    intros [C | C]; tauto.
  - specialize (IHt1 x). specialize (IHt2 x). rewrite lcontains_app.
    sinvert IHt1. { constructor. left. assumption. }
    sinvert IHt2; constructor. { right. assumption. }
    intros [C | C]; tauto.
  - rewrite lcontains_app. specialize (IHt1 x). sinvert IHt1. { constructor. left. assumption. }
    destruct (eqb_spec bind x). { subst. rewrite lminus_eq. constructor. intros [C | C]; tauto. }
    rewrite lminus_neq; [| symmetry; assumption]. specialize (IHt2 x).
    sinvert IHt2; constructor. { right. split; assumption. } intros [C | C]; tauto.
  - destruct (String.eqb_spec bound x). { constructor. left. assumption. }
    destruct (eqb_spec x rhs). { subst. rewrite lminus_eq. constructor. intros [C | C]; tauto. }
    rewrite lminus_neq; [| assumption].
    destruct (eqb_spec x lhs). { subst. rewrite lminus_eq. constructor. intros [C | C]; tauto. }
    rewrite lminus_neq; [| assumption]. specialize (IHt x).
    sinvert IHt; constructor. { right. split; [| symmetry; assumption]. split; [| symmetry]; assumption. }
    intros [C | C]; tauto.
  - destruct (String.eqb_spec bound x). { constructor. left. assumption. }
    destruct (eqb_spec x rhs). { subst. rewrite lminus_eq. constructor. intros [C | C]; tauto. }
    rewrite lminus_neq; [| assumption].
    destruct (eqb_spec x lhs). { subst. rewrite lminus_eq. constructor. intros [C | C]; tauto. }
    rewrite lminus_neq; [| assumption]. specialize (IHt x).
    sinvert IHt; constructor. { right. split; [| symmetry; assumption]. split; [| symmetry]; assumption. }
    intros [C | C]; tauto.
Qed.
Hint Resolve reflect_fv_term : core.

Inductive ctx_term : Set :=
  | CtxTmEmp
  | CtxTmVarTerm (id : string) (t : type) (tm : term)
  | CtxTmComma (lhs rhs : ctx_term)
  | CtxTmSemic (lhs rhs : ctx_term)
  .
Hint Constructors ctx_term : core.
Derive Show for ctx_term.
Derive Arbitrary for ctx_term.

(*

term_ind
	 : 
argsterm_ind
	 : forall P : argsterm -> Prop,
       
       forall a : argsterm, P a

*)
