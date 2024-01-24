From Coq Require Import
  String
  List
  Classes.EquivDec.
From LambdaST Require Import
  Ident.


From LambdaST Require Import Types.

Declare Scope term_scope.

Inductive term : Set :=
  | TmSink
  | TmUnit
  | TmVar (id : ident)
  | TmComma (lhs rhs : term)
  | TmSemic (lhs rhs : term)
  | TmLet (bind : ident) (bound body : term)
  | TmLetPar (lhs rhs bound : ident) (body : term) 
  | TmLetCat (t : type) (lhs rhs bound : ident) (body : term) 
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
Notation "'let' t ( lhs ; rhs ) = both 'in' body" :=
  (TmLetCat t lhs rhs both body) (at level 98, right associativity) : term_scope.

(* should probably be sets *)
Fixpoint fv e : list ident :=
  match e with
  | TmSink | TmUnit => nil
  | TmVar x => cons x nil
  | TmComma e1 e2 | TmSemic e1 e2 => fv e1 ++ fv e2
  | TmLet x e e' => fv e ++ remove equiv_dec x (fv e')
  | TmLetPar x y z e | TmLetCat _ x y z e => cons z (remove equiv_dec x (remove equiv_dec y (fv e)))
  end.

Inductive wf : term -> Prop :=
  | wf_TmSink : wf sink
  | wf_TmUnit : wf unit
  | wf_TmVar : forall x, wf x
  | wf_TmComma : forall e e',
      wf e ->
      wf e' ->
      wf (e , e')
  | wf_TmSemic : forall e e',
      wf e ->
      wf e' ->
      wf (e ; e')
  | wf_TmLet : forall x e e',
      wf e ->
      wf e' ->
      wf (TmLet x e e')
  | wf_TmLetPar : forall x y z e,
      wf e ->
      x <> y ->
      y <> z ->
      x <> z ->
      wf (TmLetPar x y z e)
.

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
