From LambdaST Require Import
  Derivative
  Prefix
  Types.
From Hammer Require Import
  Tactics.

(* Definition B.20 *)
Inductive PfxCat : prefix -> prefix -> prefix -> Prop :=
  | PfxCatEpsEmp :
      PfxCat PfxEpsEmp PfxEpsEmp PfxEpsEmp
  | PfxCatOneEmp : forall p,
      PfxTyped p 1 ->
      PfxCat PfxOneEmp p p
  | PfxCatOneFull :
      PfxCat PfxOneFull PfxEpsEmp PfxOneFull
  | PfxCatParPair : forall p1 p1' p1'' p2 p2' p2'',
      PfxCat p1 p1' p1'' ->
      PfxCat p2 p2' p2'' ->
      PfxCat (PfxParPair p1 p2) (PfxParPair p1' p2') (PfxParPair p1'' p2'')
  | PfxCatCatFst : forall p p' p'',
      PfxCat p p' p'' ->
      PfxCat (PfxCatFst p) (PfxCatFst p') (PfxCatFst p'')
  | PfxCatCatFstCatBoth : forall p p' p'' p''',
      PfxCat p p' p'' ->
      PfxCat (PfxCatFst p) (PfxCatBoth p' p''') (PfxCatBoth p'' p''')
  | PfxCatCatBoth : forall p p' p'' p''',
      PfxCat p' p'' p''' ->
      PfxCat (PfxCatBoth p p') p'' (PfxCatBoth p p''')
  | PfxCatSumEmp : forall p,
      PfxCat PfxSumEmp p p
  | PfxCatSumInl : forall p p' p'',
      PfxCat p' p'' p'' ->
      PfxCat (PfxSumInl p) p' (PfxSumInl p'')
  | PfxCatSumInr : forall p p' p'',
      PfxCat p p' p'' ->
      PfxCat (PfxSumInr p) p' (PfxSumInr p'')
  | PfxCatStarEmp : forall p,
      PfxCat PfxStarEmp p p
  | PfxCatStarDone :
      PfxCat PfxStarDone PfxEpsEmp PfxStarDone
  | PfxCatStarFirst : forall p p' p'',
      PfxCat p p' p'' ->
      PfxCat (PfxStarFirst p) (PfxCatFst p') (PfxStarFirst p'')
  | PfxCatStarFirstStarRest : forall p p' p'' p''',
      PfxCat p p' p'' ->
      PfxCat (PfxStarFirst p) (PfxCatBoth p' p''') (PfxStarRest p'' p''')
  | PfxCatStarRest : forall p p' p'' p''',
      PfxCat p' p'' p''' ->
      PfxCat (PfxStarRest p p') p'' (PfxStarRest p p''')
  .
Hint Constructors PfxCat : core.

(* TODO: Either something is wrong with the definition of concatenation for inl or this is just difficult *)
Lemma pfx_cat_inl_unsure : forall p' p''1 p''2,
  PfxCat p' p''1 p''1 ->
   (forall p''2, PfxCat p' p''1 p''2 -> p''1 = p''2) ->
   PfxCat p' p''2 p''2 ->
   PfxSumInl p''1 = PfxSumInl p''2.
Proof.
  intros p' p''1 p''2 H1 IH H2. f_equal. Abort.

(* Theorem B.21, part I *)
Theorem prefix_concat_unique : forall p p' p''1 p''2,
  PfxCat p p' p''1 ->
  PfxCat p p' p''2 ->
  p''1 = p''2.
Proof.
  intros p p' p''1 p''2 H1 H2. generalize dependent p''2. induction H1; intros;
  sinvert H2;
  try apply IHPfxCat in H3;
  try apply IHPfxCat in H5;
  try apply IHPfxCat in H0;
  subst; try reflexivity.
  - apply IHPfxCat1 in H5. apply IHPfxCat2 in H6. subst. reflexivity.
  - Abort. (* apply (pfx_cat_inl_unsure p'); assumption. *)

(* Theorem B.21, part II *)
Theorem prefix_concat_exists_when_typed : forall p p' s dps ,
  PfxTyped p s ->
  Derivative p s dps ->
  PfxTyped p' dps ->
  exists p'' dp'dps,
    Derivative p' dps dp'dps /\
    PfxCat p p' p'' /\
    PfxTyped p'' s /\
    Derivative p'' s dp'dps.
Proof.
  intros p p' s dps Ht Hd Ht'. generalize dependent p'. generalize dependent Ht.
  induction Hd; intros; sinvert Ht.
  - sinvert Ht'; repeat eexists; repeat constructor.
  - sinvert Ht'; repeat eexists; repeat constructor.
  - sinvert Ht'; repeat eexists; repeat constructor.
  - sinvert Ht'. specialize (IHHd1 H2). specialize (IHHd2 H4).
    apply IHHd1 in H3 as [p''1 [dp'dps1 [H21 [H22 [H23 H24]]]]].
    apply IHHd2 in H5 as [p''2 [dp'dps2 [H31 [H32 [H33 H34]]]]].
    repeat eexists; repeat constructor;
    try apply H21; try apply H31; try apply H22; try apply H32; assumption.
  - specialize (IHHd H1). sinvert Ht';
    apply IHHd in H2 as [p'' [dp'dps [h1 [h2 [h3 h4]]]]].
    + repeat eexists; repeat constructor; [apply h1 | apply h2 | |]; assumption.
    + repeat eexists; repeat constructor; try assumption.
Abort.
