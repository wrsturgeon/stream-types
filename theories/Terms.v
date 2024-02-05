From Coq Require Import String.
From Hammer Require Import Tactics.
From QuickChick Require Import QuickChick.
From LambdaST Require Import
  Eqb
  FV
  Sets
  Types.

Inductive term : Set :=
  | TmSink
  | TmUnit
  | TmVar (id : string)
  | TmComma (lhs rhs : term)
  | TmSemic (lhs rhs : term)
  | TmLet (t : type (* <-- TODO: will remove, but very helpful rn *)) (bind : string) (bound body : term)
  | TmLetPar (lhs rhs bound : string) (body : term) (* Note that the bound term is NOT really a term, but we can w.l.o.g. surround it with another `let` *)
  | TmLetCat (t : type) (lhs rhs bound : string) (body : term)
  .
Hint Constructors term : core.
Derive Show for term.
Derive Arbitrary for ascii.
Derive Arbitrary for string.
Derive Arbitrary for term.

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
  | TmLet _ x e e' => set_union (fv_term e) (set_minus (fv_term e') (singleton_set x))
  end.

Instance fv_term_inst : FV term := { fv := fv_term }.

Fixpoint lcontains {T} `{Eqb T} x li :=
  match li with
  | nil => false
  | cons hd tl => (eqb hd x || lcontains x tl)%bool
  end.

Lemma lcontains_in : forall {T} `{Eqb T} x li,
  Bool.reflect (List.In x li) (lcontains x li).
Proof.
  intros. generalize dependent H. generalize dependent x.
  induction li; cbn in *; intros. { constructor. intros []. }
  destruct (eqb_spec a x). { constructor. left. assumption. }
  specialize (IHli x H). sinvert IHli; constructor. { right. assumption. }
  intros [C | C]; tauto.
Qed.
Hint Resolve lcontains_in : core.

Lemma lcontains_app : forall {T} a b `{Eqb T} x,
  lcontains x (a ++ b) = (lcontains x a || lcontains x b)%bool.
Proof.
  induction a; cbn in *; intros. { reflexivity. }
  destruct (eqb_spec a x); cbn. { reflexivity. } apply IHa.
Qed.
Hint Resolve lcontains_app : core.

Fixpoint lminus {T} `{Eqb T} x li :=
  match li with
  | nil => nil
  | cons hd tl => if eqb x hd then lminus x tl else cons hd (lminus x tl)
  end.

Lemma lminus_eq : forall {T} li `{Eqb T} x,
  lcontains x (lminus x li) = false.
Proof.
  induction li; cbn in *; intros. { reflexivity. }
  destruct (eqb_spec x a). { apply IHli. }
  cbn. destruct (eqb_spec a x). { subst. tauto. }
  rewrite IHli. reflexivity.
Qed.

Lemma lminus_neq : forall {T} li `{Eqb T} x y,
  x <> y ->
  lcontains x (lminus y li) = lcontains x li.
Proof.
  induction li; cbn in *; intros. { reflexivity. }
  destruct (eqb_spec a x). {
    subst. destruct (eqb_spec y x). { subst. tauto. } cbn. destruct (eqb_spec x x). { reflexivity. } tauto. }
  destruct (eqb_spec y a). { subst. rewrite IHli; [| assumption]. reflexivity. }
  cbn. destruct (eqb_spec a x). { subst. tauto. } rewrite IHli; [| assumption]. reflexivity.
Qed.

Fixpoint lsubset {T} `{Eqb T} small big :=
  match small with
  | nil => true
  | cons hd tl => (lcontains hd big && lsubset tl big)%bool
  end.

Lemma lsubset_incl : forall {T} `{Eqb T} small big,
  Bool.reflect (forall x, List.In x small -> List.In x big) (lsubset small big).
Proof.
  intros. generalize dependent H. generalize dependent big.
  induction small; cbn in *; intros. { constructor. intros _ []. }
  destruct (lcontains_in a big). 2: { constructor. intro C. apply n. apply C. left. reflexivity. }
  specialize (IHsmall big H). sinvert IHsmall; constructor; intros.
  - destruct H2; [subst | apply H1]; assumption.
  - intro C. apply H1. intros. apply C. right. assumption.
Qed.
Hint Resolve lsubset_incl : core.

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
