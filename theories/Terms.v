From Coq Require Import
  String.
From LambdaST Require Import
  Ident.

Declare Scope term_scope.

Inductive term : Set :=
  | TmSink
  | TmUnit
  | TmVar (id : ident)
  | TmComma (lhs rhs : term)
  | TmSemic (lhs rhs : term)
  | TmLet (bind : ident) (bound body : term)
  | TmLetPar (lhs rhs : ident) (bound body : term) 
  | TmLetCat (lhs rhs : ident) (bound body : term) 
  .

Bind Scope term_scope with term.

Notation "'sink'" := TmSink : term_scope.
Notation "'unit'" := TmUnit : term_scope.
Notation "`id`" := (TmVar id) : term_scope.
Notation "( lhs , rhs )" := (TmComma lhs rhs) : term_scope.
Notation "( lhs ; rhs )" := (TmSemic lhs rhs) : term_scope.
Notation "'let' x = bound 'in' body" :=
  (TmLet x bound body) (at level 98, right associativity) : term_scope.
Notation "'let' ( lhs , rhs ) = both 'in' body" :=
  (TmLetPar lhs rhs both body) (at level 98, right associativity) : term_scope.
Notation "'let' ( lhs ; rhs ) = both 'in' body" :=
  (TmLetCat lhs rhs both body) (at level 98, right associativity) : term_scope.

(*
Fixpoint eq_tm lhs rhs :=
  match lhs, rhs with
  | TmSink, TmSink
  | TmUnit, TmUnit =>
      true
  | TmVar a, TmVar b =>
      a =i b
  | TmComma xl yl, TmComma xr yr
  | TmSemic xl yl, TmSemic xr yr =>
      andb (eq_tm xl yl) (eq_tm xr yr)
  | TmLetPar xl yl zl bl, TmLetPar xr yr zr br
  | TmLetCat xl yl zl bl, TmLetPar xr yr zr br =>
      andb (andb (andb
        (xl =? xr)%string
        (yl =? yr)%string)
        (eq_tm zl zr))
        (eq_tm bl br)
  | _, _ => false
  end.
*)
