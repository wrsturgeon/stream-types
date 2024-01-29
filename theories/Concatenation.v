From Hammer Require Import Tactics.
From LambdaST Require Import
  Derivative
  Prefix
  Types.

(* Definition B.20 *)
Inductive PrefixConcat : prefix -> prefix -> prefix -> Prop :=
  | PfxConcatEpsEmp :
      PrefixConcat PfxEpsEmp PfxEpsEmp PfxEpsEmp
  | PfxConcatOneEmp : forall p,
      PfxTyped p 1 ->
      PrefixConcat PfxOneEmp p p
  | PfxConcatOneFull :
      PrefixConcat PfxOneFull PfxEpsEmp PfxOneFull
  | PfxConcatParPair : forall p1 p1' p1'' p2 p2' p2'',
      PrefixConcat p1 p1' p1'' ->
      PrefixConcat p2 p2' p2'' ->
      PrefixConcat (PfxParPair p1 p2) (PfxParPair p1' p2') (PfxParPair p1'' p2'')
  | PfxConcatCatFst : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxCatFst p) (PfxCatFst p') (PfxCatFst p'')
  | PfxConcatCatFstCatBoth : forall p p' p'' p''',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxCatFst p) (PfxCatBoth p' p''') (PfxCatBoth p'' p''')
  | PfxConcatCatBoth : forall p p' p'' p''',
      PrefixConcat p' p'' p''' ->
      PrefixConcat (PfxCatBoth p p') p'' (PfxCatBoth p p''')
  | PfxConcatSumEmp : forall p,
      PrefixConcat PfxSumEmp p p
  | PfxConcatSumInl : forall p p' p'',
      PrefixConcat p' p'' p'' ->
      PrefixConcat (PfxSumInl p) p' (PfxSumInl p'')
  | PfxConcatSumInr : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxSumInr p) p' (PfxSumInr p'')
  | PfxConcatStarEmp : forall p,
      PrefixConcat PfxStarEmp p p
  | PfxConcatStarDone :
      PrefixConcat PfxStarDone PfxEpsEmp PfxStarDone
  | PfxConcatStarFirst : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxStarFirst p) (PfxCatFst p') (PfxStarFirst p'')
  | PfxConcatStarFirstStarRest : forall p p' p'' p''',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxStarFirst p) (PfxCatBoth p' p''') (PfxStarRest p'' p''')
  | PfxConcatStarRest : forall p p' p'' p''',
      PrefixConcat p' p'' p''' ->
      PrefixConcat (PfxStarRest p p') p'' (PfxStarRest p p''')
  .
Hint Constructors PrefixConcat : core.

Conjecture prefix_concat_inl_unsure : forall p' p'' : prefix,
  PrefixConcat p' p'' p'' ->
   (forall q, PrefixConcat p' p'' q -> p'' = q) ->
   forall p''0 : prefix,
   PrefixConcat p' p''0 p''0 ->
   PrefixConcat p' p'' p''0.
(*
Proof.
  intros p' p1'' p2'' H1 IH H2. apply IH. generalize dependent p2''. generalize dependent IH.
  induction H1; cbn in *; intros.
  - sauto lq: on rew: off.
  - Fail best. Abort. (* this whole thing is probably false *)
*)
Hint Resolve prefix_concat_inl_unsure : core.

(* Theorem B.21, part I *)
Theorem prefix_concat_unique : forall p p' p1'' p2'',
  PrefixConcat p p' p1'' ->
  PrefixConcat p p' p2'' ->
  p1'' = p2''.
Proof.
  intros p p' p1'' p2'' H1 H2. generalize dependent p2''. induction H1; intros;
  sinvert H2;
  try apply IHPrefixConcat in H3;
  try apply IHPrefixConcat in H5;
  try apply IHPrefixConcat in H0;
  subst; try reflexivity.
  - f_equal; [apply IHPrefixConcat1 | apply IHPrefixConcat2]; assumption.
  (* PfxConcatSumInl is the only problematic case *)
  - clear p. (* <-- something's for sure wrong *) f_equal. apply IHPrefixConcat.
    eapply prefix_concat_inl_unsure; eassumption.
Qed.
Hint Resolve prefix_concat_unique : core.

(* Theorem B.21, part II *)
Theorem prefix_concat_exists_when_typed : forall p p' s dps ,
  PfxTyped p s ->
  Derivative p s dps ->
  PfxTyped p' dps ->
  exists p'' dp'dps,
    Derivative p' dps dp'dps /\
    PrefixConcat p p' p'' /\
    PfxTyped p'' s /\
    Derivative p'' s dp'dps.
Proof.
  intros p p' s dps Ht Hd Ht'. generalize dependent p'. generalize dependent Ht.
  induction Hd; intros; sinvert Ht.
  - sinvert Ht'; repeat eexists; repeat constructor.
  - sinvert Ht'; repeat eexists; repeat constructor.
  - sinvert Ht'; repeat eexists; repeat constructor.
  - sinvert Ht'. specialize (IHHd1 H2). specialize (IHHd2 H4).
    apply IHHd1 in H3 as [p1'' [dp'dps1 [H21 [H22 [H23 H24]]]]].
    apply IHHd2 in H5 as [p2'' [dp'dps2 [H31 [H32 [H33 H34]]]]].
    repeat eexists; repeat constructor;
    try apply H21; try apply H31; try apply H22; try apply H32; assumption.
  - specialize (IHHd H1). sinvert Ht';
    apply IHHd in H2 as [p'' [dp'dps [h1 [h2 [h3 h4]]]]].
    + repeat eexists; repeat constructor; [apply h1 | apply h2 | |]; assumption.
    + repeat eexists; repeat constructor; try assumption. Abort.
