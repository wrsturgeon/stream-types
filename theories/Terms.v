From Coq Require Import
  String
  List
  Classes.EquivDec.
From LambdaST Require Import
  Ident
  FV.
From Hammer Require Import
  Tactics.
From LambdaST Require Import
  Types.

Declare Scope term_scope.

Inductive term : Set :=
  | TmSink
  | TmUnit
  | TmVar (id : ident)
  | TmComma (lhs rhs : term)
  | TmSemic (lhs rhs : term)
  | TmLetPar (lhs rhs bound : ident) (body : term)
  | TmLetCat (t : type) (lhs rhs bound : ident) (body : term)
  | TmLet (bind : ident) (bound body : term)
  | TmDrop (x : ident) (e : term)
  .
Hint Constructors term : core.

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

Fixpoint fv_term e : FV.set ident :=
  match e with
  | TmSink | TmUnit => empty_set
  | TmVar x => singleton_set x
  | TmComma e1 e2 | TmSemic e1 e2 => set_union (fv_term e1) (fv_term e2)
  | TmLetPar x y z e | TmLetCat _ x y z e => set_union (singleton_set z) (
      set_minus (set_minus (fv_term e) (singleton_set x)) (singleton_set y))
  | TmLet x e e' => set_union (fv_term e) (set_minus (fv_term e') (singleton_set x))
  | TmDrop x e => set_minus (fv_term e) (singleton_set x)
  end.

Instance fv_term_inst : FV term := { fv := fv_term }.

Fixpoint substVar (e : term) (x : ident) (y : ident) : term :=
  e.

(* term is well-formed under a set of free variables. this ensures there's no shadowing,
and all bindings are coherent. *)
(* Inductive WFTerm : set ident -> term -> Prop :=
  | WFTmSink : forall s,
      WFTerm s TmSink
  | WFTmUnit : forall s,
      WFTerm s TmUnit
  | WFTmVar : forall x s,
      s x ->
      WFTerm s (TmVar x)
  | WFTmComma : forall e e' s,
      WFTerm s e ->
      WFTerm s e' ->
      WFTerm s (e , e')
  | WFTmSemic : forall e e' s,
      WFTerm s e ->
      WFTerm s e' ->
      WFTerm s (e ; e')
  | WFTmLet : forall x e e' s,
      ~(s x) ->
      (* is this right? *)
      WFTerm s e ->
      WFTerm (set_union s (singleton_set x)) e' ->
      WFTerm s (TmLet x e e')
  | WFTmLetPar : forall x y z e s,
      WFTerm (set_union (set_minus s (singleton_set z)) (set_union (singleton_set x) (singleton_set y))) e ->
      s z ->
      ~(s x) ->
      ~(s y) ->
      x <> y ->
      WFTerm s (TmLetPar x y z e)
  | WFTmLetCat : forall x y z e t s,
      WFTerm (set_union (set_minus s (singleton_set z)) (set_union (singleton_set x) (singleton_set y))) e ->
      s z ->
      ~(s x) ->
      ~(s y) ->
      x <> y ->
      WFTerm s (TmLetCat t x y z e)
.

Theorem wf_iff : forall s s' e,
  SetEq s s' ->
  WFTerm s e ->
  WFTerm s' e.
Proof.
  intros.
  generalize dependent s'.
  induction H0; sauto.
Qed. *)
