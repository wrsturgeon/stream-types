From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From Coq Require Import String.
From LambdaST Require Import Eqb.

Declare Scope term_scope.

Inductive term : Set :=
  | TmSink
  | TmUnit
  | TmVar (id : string)
  | TmComma (lhs rhs : term)
  | TmSemic (lhs rhs : term)
  | TmLet (bind : string) (bound body : term)
  | TmLetPar (lhs rhs bound : string) (body : term) (* Note that the bound term is NOT really a term, but we can w.l.o.g. surround it with another `let` *)
  | TmLetCat (lhs rhs bound : string) (body : term) 
  .
Hint Constructors term : core.
Derive Show for term.
Derive Arbitrary for ascii.
Derive Arbitrary for string.
Derive Arbitrary for term.

Bind Scope term_scope with term.

Notation "'sink'" := TmSink : term_scope.
Notation "'unit'" := TmUnit : term_scope.
Notation "`id`" := (TmVar id) : term_scope.
Notation "( lhs , rhs )" := (TmComma lhs rhs) : term_scope.
Notation "( lhs ; rhs )" := (TmSemic lhs rhs) : term_scope.
Notation "'let' x = bound 'in' body" :=
  (TmLet x bound body) (at level 97, right associativity) : term_scope.
Notation "'let' ( lhs , rhs ) = both 'in' body" :=
  (TmLetPar lhs rhs both body) (at level 97, right associativity) : term_scope.
Notation "'let' ( lhs ; rhs ) = both 'in' body" :=
  (TmLetCat lhs rhs both body) (at level 97, right associativity) : term_scope.

Fixpoint term_size t :=
  match t with
  | TmSink
  | TmUnit
  | TmVar _ =>
      1
  | TmComma lhs rhs
  | TmSemic lhs rhs
  | TmLet _ lhs rhs =>
      1 + term_size lhs + term_size rhs
  | TmLetPar _ _ _ body
  | TmLetCat _ _ _ body =>
      1 + term_size body
  end.

(*
Fail Fixpoint eq_tm lhs rhs :=
  match lhs, rhs with
  | TmSink, TmSink
  | TmUnit, TmUnit =>
      true
  | TmVar a, TmVar b =>
      String.eqb a b
  | TmComma xl yl, TmComma xr yr
  | TmSemic xl yl, TmSemic xr yr =>
      andb (eq_tm xl yl) (eq_tm xr yr)
  | TmLetPar xl yl zl bl, TmLetPar xr yr zr br
  | TmLetCat xl yl zl bl, TmLetPar xr yr zr br =>
      andb (andb (andb
        (String.eqb xl xr)
        (String.eqb yl yr))
        (String.eqb zl zr))
        (eq_tm bl br)
  | _, _ => false
  end.
*)

(* Can't believe I just found out you can do this: *)
Scheme Equality for term. (* <-- no fucking way *)
Theorem eqb_spec_term : forall a b : term, Bool.reflect (a = b) (term_beq a b).
Proof.
  intros. destruct (term_beq a b) eqn:E; constructor;
  sfirstorder use: internal_term_dec_bl, internal_term_dec_lb.
Qed.
Instance eqb_term : Eqb term := { eqb := term_beq; eq_dec := term_eq_dec; eqb_spec := eqb_spec_term }.
Hint Unfold term_beq : core.
Hint Resolve term_eq_dec : core.
Hint Resolve eqb_spec_term : core.
