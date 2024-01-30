From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From Coq Require Import String.
From LambdaST Require Import
  Eqb
  Sets
  Types.

Declare Scope term_scope.

Inductive term : Set :=
  | TmSink
  | TmUnit
  | TmVar (id : string)
  | TmComma (lhs rhs : term)
  | TmSemic (lhs rhs : term)
  | TmLet (bind : string) (bound body : term)
  | TmLetPar (lhs rhs bound : string) (body : term) (* Note that the bound term is NOT really a term, but we can w.l.o.g. surround it with another `let` *)
  | TmLetCat (t : type) (lhs rhs bound : string) (body : term)
  | TmDrop (x : string) (e : term)
  .
Hint Constructors term : core.
Derive Show for term.
Derive Arbitrary for ascii.
Derive Arbitrary for string.
Derive Arbitrary for term.

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
Notation "'drop' x ';' body" :=
  (TmDrop x body) (at level 97, right associativity) : term_scope.

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

Inductive WFTerm : set string -> term -> Prop :=
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
      WFTerm s (e, e')
  | WFTmSemic : forall e e' s,
      WFTerm s e ->
      WFTerm s e' ->
      WFTerm s (e; e')
  | WFTmLet : forall x e e' s,
      ~s x ->
      (* is this right? *)
      WFTerm s e ->
      WFTerm (set_union s (singleton_set x)) e' ->
      WFTerm s (TmLet x e e')
  | WFTmLetPar : forall x y z e s,
      WFTerm (set_union (set_minus s (singleton_set z)) (set_union (singleton_set x) (singleton_set y))) e ->
      s z ->
      ~s x ->
      ~s y ->
      x <> y ->
      WFTerm s (TmLetPar x y z e)
  | WFTmLetCat : forall x y z e t s,
      WFTerm (set_union (set_minus s (singleton_set z)) (set_union (singleton_set x) (singleton_set y))) e ->
      s z ->
      ~s x ->
      ~s y ->
      x <> y ->
      (* TODO: WFType s t -> *)
      WFTerm s (TmLetCat t x y z e)
.
Hint Constructors WFTerm : core.

Theorem wf_iff : forall s s' e,
  SetEq s s' ->
  WFTerm s e ->
  WFTerm s' e.
Proof.
  intros.
  generalize dependent s'.
  induction H0; cbn in *; intros; constructor; sfirstorder.
Qed.
