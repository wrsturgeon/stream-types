From QuickChick Require Import QuickChick.
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
Derive Show for prefix.
Derive Arbitrary for prefix.

Inductive Maximal : prefix -> Prop :=
  | MaxEpsEmp :
      Maximal PfxEpsEmp
  | MaxOneFull :
      Maximal PfxOneFull
  | MaxParPair : forall p1 p2,
      Maximal p1 ->
      Maximal p2 ->
      Maximal (PfxParPair p1 p2)
  | MaxCatBoth : forall p1 p2,
      Maximal p1 ->
      Maximal p2 ->
      Maximal (PfxCatBoth p1 p2)
  | MaxSumInl : forall p,
      Maximal p ->
      Maximal (PfxSumInl p)
  | MaxSumInr : forall p,
      Maximal p ->
      Maximal (PfxSumInr p)
  | MaxStarDone :
      Maximal PfxStarDone
  | MaxStarRest : forall p p',
      Maximal p ->
      Maximal p' ->
      Maximal (PfxStarRest p p')
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
      Maximal p1 ->
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
      Maximal p ->
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

Inductive Empty : prefix -> Prop :=
  | EmptyEpsEmp :
      Empty PfxEpsEmp
  | EmptyOneEmp :
      Empty PfxOneEmp
  | EmptyParPair : forall p1 p2,
      Empty p1 ->
      Empty p2 ->
      Empty (PfxParPair p1 p2)
  | EmptyCatFst : forall p,
      Empty p ->
      Empty (PfxCatFst p)
  | EmptySumEmp :
      Empty PfxSumEmp
  .
Hint Constructors Empty : core.

Definition EmptyOn (s : Set) : (s -> prefix) -> Prop := fun n => forall (x : s), let p := n x in Empty p.
Hint Unfold EmptyOn : core.
Definition MaximalOn (s : Set) : (s -> prefix) -> Prop := fun n => forall (x : s), let p := n x in Maximal p.
Hint Unfold MaximalOn : core.
