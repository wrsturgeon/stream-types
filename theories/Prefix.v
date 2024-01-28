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

Inductive MaximalPrefix : prefix -> Prop :=
  | PfxMaxEpsEmp :
      MaximalPrefix PfxEpsEmp
  | PfxMaxOneFull :
      MaximalPrefix PfxOneFull
  | PfxMaxParPair : forall p1 p2,
      MaximalPrefix p1 ->
      MaximalPrefix p2 ->
      MaximalPrefix (PfxParPair p1 p2)
  | PfxMaxCatBoth : forall p1 p2,
      MaximalPrefix p1 ->
      MaximalPrefix p2 ->
      MaximalPrefix (PfxCatBoth p1 p2)
  | PfxMaxSumInl : forall p,
      MaximalPrefix p ->
      MaximalPrefix (PfxSumInl p)
  | PfxMaxSumInr : forall p,
      MaximalPrefix p ->
      MaximalPrefix (PfxSumInr p)
  | PfxMaxStarDone :
      MaximalPrefix PfxStarDone
  | PfxMaxStarRest : forall p p',
      MaximalPrefix p ->
      MaximalPrefix p' ->
      MaximalPrefix (PfxStarRest p p')
  .
Hint Constructors Maximal : core.

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
      MaximalPrefix p1 ->
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
      MaximalPrefix p ->
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

Inductive EmptyPrefix : prefix -> Prop :=
  | EmptyPrefixEpsEmp :
      EmptyPrefix PfxEpsEmp
  | EmptyPrefixOneEmp :
      EmptyPrefix PfxOneEmp
  | EmptyPrefixParPair : forall p1 p2,
      EmptyPrefix p1 ->
      EmptyPrefix p2 ->
      EmptyPrefix (PfxParPair p1 p2)
  | EmptyPrefixCatFst : forall p,
      EmptyPrefix p ->
      EmptyPrefix (PfxCatFst p)
  | EmptyPrefixSumEmp :
      EmptyPrefix PfxSumEmp
  .
Hint Constructors Empty : core.

Definition EmptyPrefixOn (s : Set) : (s -> prefix) -> Prop := fun n => forall (x : s), let p := n x in EmptyPrefix p.
Hint Unfold EmptyOn : core.
Definition MaximalPrefixOn (s : Set) : (s -> prefix) -> Prop := fun n => forall (x : s), let p := n x in MaximalPrefix p.
Hint Unfold MaximalOn : core.
