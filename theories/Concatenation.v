From Hammer Require Import Tactics.
From LambdaST Require Import
  Derivative
  Prefix
  Types.

(* Definition B.20 *)
Inductive PrefixConcat : prefix -> prefix -> prefix -> Prop :=
  | PfxCatEpsEmp :
      PrefixConcat PfxEpsEmp PfxEpsEmp PfxEpsEmp
  | PfxCatOneEmp : forall p,
      PrefixTyped p 1 ->
      PrefixConcat PfxOneEmp p p
  | PfxCatOneFull :
      PrefixConcat PfxOneFull PfxEpsEmp PfxOneFull
  | PfxCatParPair : forall p1 p1' p1'' p2 p2' p2'',
      PrefixConcat p1 p1' p1'' ->
      PrefixConcat p2 p2' p2'' ->
      PrefixConcat (PfxParPair p1 p2) (PfxParPair p1' p2') (PfxParPair p1'' p2'')
  | PfxCatCatFst : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxCatFst p) (PfxCatFst p') (PfxCatFst p'')
  | PfxCatCatFstCatBoth : forall p p' p'' p''',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxCatFst p) (PfxCatBoth p' p''') (PfxCatBoth p'' p''')
  | PfxCatCatBoth : forall p p' p'' p''',
      PrefixConcat p' p'' p''' ->
      PrefixConcat (PfxCatBoth p p') p'' (PfxCatBoth p p''')
  | PfxCatSumEmp : forall p,
      PrefixConcat PfxSumEmp p p
  | PfxCatSumInl : forall p p' p'',
      PrefixConcat p p' p'' -> (* <-- TODO: Make sure this was a typo in the Appendix! *)
      PrefixConcat (PfxSumInl p) p' (PfxSumInl p'')
  | PfxCatSumInr : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxSumInr p) p' (PfxSumInr p'')
  | PfxCatStarEmp : forall p,
      PrefixConcat PfxStarEmp p p
  | PfxCatStarDone :
      PrefixConcat PfxStarDone PfxEpsEmp PfxStarDone
  | PfxCatStarFirst : forall p p' p'',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxStarFirst p) (PfxCatFst p') (PfxStarFirst p'')
  | PfxCatStarFirstStarRest : forall p p' p'' p''',
      PrefixConcat p p' p'' ->
      PrefixConcat (PfxStarFirst p) (PfxCatBoth p' p''') (PfxStarRest p'' p''')
  | PfxCatStarRest : forall p p' p'' p''',
      PrefixConcat p' p'' p''' ->
      PrefixConcat (PfxStarRest p p') p'' (PfxStarRest p p''')
  .
Hint Constructors PrefixConcat : core.

(* Theorem B.21, part I *)
Theorem prefix_concat_unique : forall p p' p1'' p2'',
  PrefixConcat p p' p1'' ->
  PrefixConcat p p' p2'' ->
  p1'' = p2''.
Proof.
  intros p p' p1'' p2'' H1 H2. generalize dependent p2''. induction H1; intros; sinvert H2;
  try apply IHPrefixConcat in H3;
  try apply IHPrefixConcat in H5;
  try apply IHPrefixConcat in H0;
  subst; try reflexivity.
  f_equal; [apply IHPrefixConcat1 | apply IHPrefixConcat2]; assumption.
Qed.
Hint Resolve prefix_concat_unique : core.

(*
(* Theorem B.21, part II *)
Theorem prefix_concat_exists_when_typed : forall p p' s dps dp'dps,
  Derivative p s dps -> (* i.e., d_p(s) = `dps`. difficult to write in ASCII *)
  Derivative p' dps dp'dps -> (* i.e. d_{p'}(d_p(s)) = `dp'dps` *)
  PrefixTyped p s ->
  PrefixTyped p' dps ->
  exists p'',
  PrefixConcat p p' p'' /\ (* from "such a p'' exists" *)
  PrefixTyped p'' s /\
  Derivative p'' s dp'dps.
Proof.
<<<<<<< HEAD
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
=======
  intros p p' s dps dp'dps Hd Hd' Ht Ht'. generalize dependent p'. generalize dependent dps.
  generalize dependent dp'dps. induction Ht; cbn in *; intros; sinvert Hd.
  - eexists. repeat split; [| eassumption | assumption]. invert Ht'. constructor.
  - sfirstorder.
  - sauto lq: on.
  - sinvert Ht'. sinvert Hd'.
    destruct (IHHt1 _ _ H4 _ H8 H2) as [P1 [Hpc1 [Hpt1 Hd1]]]; clear IHHt1.
    destruct (IHHt2 _ _ H5 _ H9 H3) as [P2 [Hpc2 [Hpt2 Hd2]]]; clear IHHt2.
    eexists. repeat constructor; eassumption.
  - sinvert Hd'. { sauto lq: on. } sinvert Ht'. Fail best. Abort.
>>>>>>> origin/main
*)


(* TODO: prefix concatenation and derivatives,*)
(* TODO: prefix concatenation is associative. *)
(* TODO: environment concatenation, and the same. Environment concat: n . n' ~ n'' if,
for all x in dom(n) and dom(n'), n(x) . n'(x) ~ n''(x)*)