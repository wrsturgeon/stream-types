From Coq Require Import
  String
  List
  Classes.EquivDec.
From LambdaST Require Import
  Ident
  FV.

From Hammer Require Import Tactics.

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

(* term is well-formed under a set of free variables. this ensures there's no shadowing, 
and all bindings are coherent. *)
Inductive wf : set ident -> term -> Prop :=
  | wf_TmSink : forall s, wf s TmSink
  | wf_TmUnit : forall s, wf s TmUnit
  | wf_TmVar : forall x s, s x -> wf s (TmVar x)
  | wf_TmComma : forall e e' s,
      wf s e ->
      wf s e' ->
      wf s (e , e')
  | wf_TmSemic : forall e e' s,
      wf s e ->
      wf s e' ->
      wf s (e ; e')
  | wf_TmLet : forall x e e' s,
      ~(s x) ->
      (* is this right? *)
      wf s e ->
      wf (union s (singleton x)) e' ->
      wf s (TmLet x e e')
  | wf_TmLetPar : forall x y z e s,
      wf (union (minus s (singleton z)) (union (singleton x) (singleton y))) e ->
      s z ->
      ~(s x) ->
      ~(s y) ->
      x <> y ->
      wf s (TmLetPar x y z e)
  | wf_TmLetCat : forall x y z e t s,
      wf (union (minus s (singleton z)) (union (singleton x) (singleton y))) e ->
      s z ->
      ~(s x) ->
      ~(s y) ->
      x <> y ->
      wf s (TmLetCat t x y z e)
.

Theorem wf_iff : forall s s' e, (forall x, s x <-> s' x) -> wf s e -> wf s' e.
Proof.
  intros.
  generalize dependent s'.
  induction H0; sauto.
Qed.
