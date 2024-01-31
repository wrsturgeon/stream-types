From Coq Require Import String.
From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Eqb
  FV
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

Scheme Equality for term.
Theorem eqb_spec_term : forall a b : term, Bool.reflect (a = b) (term_beq a b).
Proof.
  intros. destruct (term_beq a b) eqn:E; constructor;
  sfirstorder use: internal_term_dec_bl, internal_term_dec_lb.
Qed.
Instance eqb_term : Eqb term := { eqb := term_beq; eq_dec := term_eq_dec; eqb_spec := eqb_spec_term }.
Hint Unfold term_beq : core.
Hint Resolve term_eq_dec : core.
Hint Resolve eqb_spec_term : core.

Fixpoint fv_term e : set string :=
  match e with
  | TmSink | TmUnit => empty_set
  | TmVar x => singleton_set x
  | TmComma e1 e2 | TmSemic e1 e2 => set_union (fv_term e1) (fv_term e2)
  | TmLetPar x y z e | TmLetCat _ x y z e => set_union (singleton_set z) (
      set_minus (set_minus (fv_term e) (singleton_set x)) (singleton_set y))
  | TmLet x e e' => set_union (fv_term e) (set_minus (fv_term e') (singleton_set x))
  | TmDrop x e => set_union (fv_term e) (singleton_set x)
  end.

Instance fv_term_inst : FV term := { fv := fv_term }.

Inductive Inert : term -> Prop :=
  | InertParR : forall e1 e2,
      Inert e1 ->
      Inert e2 ->
      Inert (e1, e2)
  | InertParL : forall x y z e ,
      Inert e ->
      Inert (TmLetPar x y z e)
  | InertCatL : forall t x y z e,
      Inert e ->
      Inert (TmLetCat t x y z e)
  | InertEpsR : Inert sink
  | InertVar : forall x,
      Inert (TmVar x)
  | InertLet : forall x e e',
      Inert e ->
      Inert e' ->
      Inert (TmLet x e e')
  | InertDrop : forall x e ,
      Inert e ->
      Inert (drop x; e)
  .
Hint Constructors Inert : core.

(*
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
      WFTerm s e ->
      WFTerm (set_union s (singleton_set x)) e' ->
      WFTerm s (TmLet x e e')
  | WFTmLetPar : forall x y z e s,
      s z ->
      ~s x ->
      ~s y ->
      x <> y ->
      WFTerm (set_minus (set_union s (set_union (singleton_set x) (singleton_set y))) (singleton_set z)) e ->
      WFTerm s (TmLetPar x y z e)
  | WFTmLetCat : forall x y z e t s,
      s z ->
      ~s x ->
      ~s y ->
      x <> y ->
      (* TODO: WFType s t -> *)
      WFTerm (set_minus (set_union s (set_union (singleton_set x) (singleton_set y))) (singleton_set z)) e ->
      WFTerm s (TmLetCat t x y z e)
.
Hint Constructors WFTerm : core.

Lemma wf_set_eq : forall s s' e,
  SetEq s s' ->
  WFTerm s e ->
  WFTerm s' e.
Proof.
  intros.
  generalize dependent s'.
  induction H0; cbn in *; intros; constructor; sfirstorder.
Qed.

(* TODO: it is a bit concerning that we can't prove this *)
Lemma wf_weaken_l : forall sl sr x,
  (forall z, fv x z -> sl z) -> (* <-- i.e., sl contains all the free variables in x *)
  WFTerm (set_union sl sr) x ->
  WFTerm sl x.
Proof.
  (*
  intros sl sr x Hf H. remember (set_union sl sr) as s eqn:Es. generalize dependent sl. generalize dependent sr.
  induction H; intros; subst; cbn in *.
  - constructor.
  - constructor.
  - constructor. apply Hf. reflexivity.
  - constructor; [eapply IHWFTerm1 | eapply IHWFTerm2]; sfirstorder.
  - constructor; [eapply IHWFTerm1 | eapply IHWFTerm2]; sfirstorder.
  - constructor; [sfirstorder | eapply IHWFTerm1; sfirstorder | eapply IHWFTerm2]; clear IHWFTerm1 IHWFTerm2.
    admit. cbn. rewrite or_assoc.
    shelve. shelve.
  - constructor; [shelve | sfirstorder | sfirstorder | sfirstorder | sfirstorder].
  - constructor; [shelve | sfirstorder | sfirstorder | sfirstorder | sfirstorder].
  Unshelve. Abort.
  *)
  intros sl sr x. generalize dependent sl. generalize dependent sr. induction x; cbn in *; intros.
  - (* sink *)
    constructor.
  - (* unit *)
    constructor.
  - (* Var id *)
    constructor. apply H. reflexivity.
  - (* (x1, x2) *)
    invert H0. constructor; [eapply IHx1 | eapply IHx2]; sfirstorder.
  - (* (x1; x2) *)
    sinvert H0. constructor; [eapply IHx1 | eapply IHx2]; sfirstorder.
  - (* let bind = x1 in x2 *)
    shelve. (* sinvert H0. cbn in H7. constructor; [sfirstorder | sfirstorder |]. cbn. eapply IHx2. best. ; [eapply IHx1 | eapply IHx2]; sfirstorder. *)
  - (* let (lhs, rhs) = bound in x *)
    sinvert H0. constructor; [sfirstorder | sfirstorder | sfirstorder | sfirstorder |]. cbn in *.
    eapply IHx. { shelve. } eapply wf_set_eq; [| eassumption]. cbn. intro x'. split; intro H'. { sfirstorder. }
    destruct H'. { destruct H0. split; [| assumption]. destruct H0; [| right; assumption]. sfirstorder. }
    split. { left. right. assumption. } intro. subst. (* Need to show that `sr` does not contain `bound` *) Abort.
*)
