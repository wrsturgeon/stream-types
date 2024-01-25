From Coq Require Import
  String
  List
  Classes.EquivDec.
From LambdaST Require Import
  Ident
  FV.


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

Fixpoint term_fv e : FV.set ident :=
  match e with
  | TmSink | TmUnit => empty
  | TmVar x => singleton x
  | TmComma e1 e2 | TmSemic e1 e2 => union (term_fv e1) (term_fv e2)
  | TmLet x e e' => union (term_fv e) (minus (term_fv e') (singleton x))
  | TmLetPar x y z e | TmLetCat _ x y z e => union (singleton z) (minus (minus (term_fv e) (singleton x)) (singleton y))
  end.

Instance term_fv_inst : FV term :=
{
  fv := term_fv
}.

Inductive wf : term -> Prop :=
  | wf_TmSink : wf TmSink
  | wf_TmUnit : wf TmUnit
  | wf_TmVar : forall x , wf (TmVar x)
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
  | wf_TmLetCat : forall x y z e t,
      wf e ->
      x <> y ->
      y <> z ->
      x <> z ->
      wf (TmLetCat t x y z e)
.