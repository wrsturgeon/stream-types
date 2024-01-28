From LambdaST Require Import
  Types.

Inductive prefix : Set :=
  | PfxOneEmp
  | PfxOneFull
  | PfxEpsEmp
  | PfxParPair (p p' : prefix)
  | PfxCatFst (p : prefix)
  | PfxCatBoth (b p : prefix)
  | PfxSumEmp
  | PfxSumInl (p : prefix)
  | PfxSumInr (p : prefix)
  | PfxStarEmp
  | PfxStarDone
  | PfxStarFirst (p : prefix)
  | PfxStarRest (b p : prefix)
  .
Hint Constructors prefix : core.

Inductive MaximalPfx : prefix -> Prop :=
  | MaxEpsEmp :
      MaximalPfx PfxEpsEmp
  | MaxOneFull :
      MaximalPfx PfxOneFull
  | MaxParPair : forall p1 p2,
      MaximalPfx p1 ->
      MaximalPfx p2 ->
      MaximalPfx (PfxParPair p1 p2)
  | MaxCatBoth : forall p1 p2,
      MaximalPfx p1 ->
      MaximalPfx p2 ->
      MaximalPfx (PfxCatBoth p1 p2)
  | MaxSumInl : forall p,
      MaximalPfx p ->
      MaximalPfx (PfxSumInl p)
  | MaxSumInr : forall p,
      MaximalPfx p ->
      MaximalPfx (PfxSumInr p)
  | MaxStarDone :
      MaximalPfx PfxStarDone
  | MaxStarRest : forall p p',
      MaximalPfx p ->
      MaximalPfx p' ->
      MaximalPfx (PfxStarRest p p')
  .
Hint Constructors MaximalPfx : core.

Inductive PfxTyped : prefix -> type -> Prop :=
  | PfxTyEpsEmp :
      PfxTyped PfxEpsEmp eps
  | PfxTyOneEmp :
      PfxTyped PfxOneEmp 1
  | PfxTyOneFull :
      PfxTyped PfxOneFull 1
  | PfxTyParPair : forall p1 p2 s t,
      PfxTyped p1 s ->
      PfxTyped p2 t ->
      PfxTyped (PfxParPair p1 p2) (TyPar s t)
  | PfxTyCatFst : forall p s t,
      PfxTyped p s ->
      PfxTyped (PfxCatFst p) (TyDot s t)
  | PfxTyCatBoth : forall p1 p2 s t,
      PfxTyped p1 s ->
      MaximalPfx p1 ->
      PfxTyped p2 t ->
      PfxTyped (PfxCatBoth p1 p2) (TyDot s t)
  | PfxTySumEmp : forall s t,
      PfxTyped PfxSumEmp (TySum s t)
  | PfxTySumInl : forall p s t,
      PfxTyped p s ->
      PfxTyped (PfxSumInl p) (TySum s t)
  | PfxTySumInr : forall p s t,
      PfxTyped p t ->
      PfxTyped (PfxSumInr p) (TySum s t)
  | PfxTyStarEmp : forall s,
      PfxTyped PfxStarEmp (TyStar s)
  | PfxTyStarDone : forall s,
      PfxTyped PfxStarDone (TyStar s)
  | PfxTyStarFirst : forall p s,
      PfxTyped p s ->
      PfxTyped (PfxStarFirst p) (TyStar s)
  | PfxTyStarRest : forall p p' s,
      PfxTyped p s ->
      MaximalPfx p ->
      PfxTyped p' (TyStar s) ->
      PfxTyped (PfxStarRest p p') (TyStar s)
  .
Hint Constructors PfxTyped : core.

Fixpoint emp ty :=
  match ty with
  | TyEps => PfxEpsEmp
  | TyOne => PfxOneEmp
  | TyDot s _ => PfxCatFst (emp s)
  | TyPar s t => PfxParPair (emp s) (emp t)
  | TySum _ _ => PfxSumEmp
  | TyStar _ => PfxStarEmp
  end.

Theorem emp_well_typed : forall s, PfxTyped (emp s) s.
Proof. induction s; cbn; constructor; assumption. Qed.
Hint Resolve emp_well_typed : core.

Inductive EmptyPfx : prefix -> Prop :=
  | EmptyPfxEpsEmp :
      EmptyPfx PfxEpsEmp
  | EmptyPfxOneEmp :
      EmptyPfx PfxOneEmp
  | EmptyPfxParPair : forall p1 p2,
      EmptyPfx p1 ->
      EmptyPfx p2 ->
      EmptyPfx (PfxParPair p1 p2)
  | EmptyPfxCatFst : forall p,
      EmptyPfx p ->
      EmptyPfx (PfxCatFst p)
  | EmptyPfxSumEmp :
      EmptyPfx PfxSumEmp
  .
Hint Constructors EmptyPfx : core.

Definition EmptyOnSet (s : Set) (n : s -> prefix) : Prop := forall x, EmptyPfx (n x).
Hint Unfold EmptyOnSet : core.
Definition MaximalOnSet (s : Set) (n : s -> prefix) : Prop := forall x, MaximalPfx (n x).
Hint Unfold MaximalOnSet : core.
