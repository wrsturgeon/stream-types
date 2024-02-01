From QuickChick Require Import QuickChick.
From LambdaST Require Import Types.

Inductive prefix : Set :=
    (* Expecting a 1, not received yet *)
  | PfxOneEmp
    (* Received a 1 *)
  | PfxOneFull
    (* Expecting nothing *)
  | PfxEpsEmp
    (* Everything you've already received in a parallel stream, no matter which side *)
  | PfxParPair (p p' : prefix)
    (* First part of a concatenation (hasn't switched over to the second yet) *)
  | PfxCatFst (p : prefix)
    (* Second half of a concat (first part exhausted) *)
  | PfxCatBoth (b p : prefix)
    (* Expecting a stream of either one type or another, nothing received yet *)
  | PfxSumEmp
    (* Got the first bit of a stream of type (whatever was on the left of the `+`) *)
  | PfxSumInl (p : prefix)
    (* Got the first bit of a stream of type (whatever was on the right of the `+`) *)
  | PfxSumInr (p : prefix)
    (* Expecting a star, nothing received yet *)
  | PfxStarEmp
    (* Trivial end-cap to a star *)
  | PfxStarDone
    (* First element in a star *)
  | PfxStarFirst (p : prefix)
    (* Basically `cons` in time *)
  | PfxStarRest (b p : prefix)
  .
Hint Constructors prefix : core.
Derive Show for prefix.
Derive Arbitrary for prefix.

Inductive MaximalPrefix : prefix -> Prop :=
    (* If you weren't expecting anything, you've received all the nothing you'll get *)
  | MaxPfxEpsEmp :
      MaximalPrefix PfxEpsEmp
    (* Expected a 1 and got it *)
  | MaxPfxOneFull :
      MaximalPrefix PfxOneFull
    (* In a parallel setting, both streams have independently been exhausted *)
  | MaxPfxParPair : forall p1 p2,
      MaximalPrefix p1 ->
      MaximalPrefix p2 ->
      MaximalPrefix (PfxParPair p1 p2)
    (* Received two exhausted streams, concatenated *)
  | MaxPfxCatBoth : forall p1 p2,
      MaximalPrefix p1 ->
      MaximalPrefix p2 ->
      MaximalPrefix (PfxCatBoth p1 p2)
    (* Got a stream on the left of a sum and exhausted it *)
  | MaxPfxSumInl : forall p,
      MaximalPrefix p ->
      MaximalPrefix (PfxSumInl p)
    (* Got a stream on the right of a sum and exhausted it *)
  | MaxPfxSumInr : forall p,
      MaximalPrefix p ->
      MaximalPrefix (PfxSumInr p)
    (* Received all of a star *)
  | MaxPfxStarDone :
      MaximalPrefix PfxStarDone
    (* I believe this kind of uses the above rule as a subroutine: whenever starDone is on the right, ... *)
  | MaxPfxStarRest : forall p p',
      MaximalPrefix p ->
      MaximalPrefix p' ->
      MaximalPrefix (PfxStarRest p p')
  .
Hint Constructors MaximalPrefix : core.

(* This is all pretty intuitive once you get the above *)
Inductive PrefixTyped : prefix -> type -> Prop :=
  | PfxTyEpsEmp :
      PrefixTyped PfxEpsEmp eps
  | PfxTyOneEmp :
      PrefixTyped PfxOneEmp 1
  | PfxTyOneFull :
      PrefixTyped PfxOneFull 1
  | PfxTyParPair : forall p1 p2 s t,
      PrefixTyped p1 s ->
      PrefixTyped p2 t ->
      PrefixTyped (PfxParPair p1 p2) (TyPar s t)
  | PfxTyCatFst : forall p s t,
      PrefixTyped p s ->
      PrefixTyped (PfxCatFst p) (TyDot s t)
  | PfxTyCatBoth : forall p1 p2 s t,
      PrefixTyped p1 s ->
      MaximalPrefix p1 ->
      PrefixTyped p2 t ->
      PrefixTyped (PfxCatBoth p1 p2) (TyDot s t)
  | PfxTySumEmp : forall s t,
      PrefixTyped PfxSumEmp (TySum s t)
  | PfxTySumInl : forall p s t,
      PrefixTyped p s ->
      PrefixTyped (PfxSumInl p) (TySum s t)
  | PfxTySumInr : forall p s t,
      PrefixTyped p t ->
      PrefixTyped (PfxSumInr p) (TySum s t)
  | PfxTyStarEmp : forall s,
      PrefixTyped PfxStarEmp (TyStar s)
  | PfxTyStarDone : forall s,
      PrefixTyped PfxStarDone (TyStar s)
  | PfxTyStarFirst : forall p s,
      PrefixTyped p s ->
      PrefixTyped (PfxStarFirst p) (TyStar s)
  | PfxTyStarRest : forall p p' s,
      PrefixTyped p s ->
      MaximalPrefix p ->
      PrefixTyped p' (TyStar s) ->
      PrefixTyped (PfxStarRest p p') (TyStar s)
  .
Hint Constructors PrefixTyped : core.

Fixpoint emp ty :=
  match ty with
  | TyEps => PfxEpsEmp
  | TyOne => PfxOneEmp
  | TyDot s _ => PfxCatFst (emp s)
  | TyPar s t => PfxParPair (emp s) (emp t)
  | TySum _ _ => PfxSumEmp
  | TyStar _ => PfxStarEmp
  end.

Theorem emp_well_typed : forall s, PrefixTyped (emp s) s.
Proof. induction s; cbn; constructor; assumption. Qed.
Hint Resolve emp_well_typed : core.

Inductive EmptyPrefix : prefix -> Prop :=
  | EmptyPfxEpsEmp :
      EmptyPrefix PfxEpsEmp
  | EmptyPfxOneEmp :
      EmptyPrefix PfxOneEmp
  | EmptyPfxParPair : forall p1 p2,
      EmptyPrefix p1 ->
      EmptyPrefix p2 ->
      EmptyPrefix (PfxParPair p1 p2)
  | EmptyPfxCatFst : forall p,
      EmptyPrefix p ->
      EmptyPrefix (PfxCatFst p)
  | EmptyPfxSumEmp :
      EmptyPrefix PfxSumEmp
  .
Hint Constructors EmptyPrefix : core.
