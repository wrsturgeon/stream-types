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
      PrefixConcat p p' p'' -> (* <-- TODO: Was this a typo in the Appendix? *)
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
Theorem pfx_cat_unique : forall p p' p1'' p2'',
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
Hint Resolve pfx_cat_unique : core.

(* Theorem B.21, part II *)
Theorem pfx_cat_exists_when_typed : forall p p' s dps dp'dps,
  Derivative p s dps -> (* i.e., d_p(s) = `dps`. difficult to write in ASCII *)
  Derivative p' dps dp'dps -> (* i.e. d_{p'}(d_p(s)) = `dp'dps` *)
  PrefixTyped p s ->
  PrefixTyped p' dps ->
  exists p'',
  PrefixConcat p p' p'' /\ (* from "such a p'' exists" *)
  PrefixTyped p'' s /\
  Derivative p'' s dp'dps.
Proof.
  intros p p' s dps dp'dps Hd Hd' Hp Hp'. generalize dependent p'. generalize dependent dp'dps.
  generalize dependent Hp. induction Hd; intros; simpl in *.
  - sinvert Hp. sinvert Hd'. sinvert Hp'. eexists. repeat constructor.
  - sinvert Hp. eexists. split; [constructor | split]; assumption.
  - sinvert Hp. sinvert Hd'. sinvert Hp'. eexists. repeat constructor.
  - sinvert Hp. sinvert Hd'. sinvert Hp'.
    specialize (IHHd1 H2 _ _ H3 H5) as [p1'' [Hp1a [Hp1b Hp1c]]].
    specialize (IHHd2 H4 _ _ H6 H8) as [p2'' [Hp2a [Hp2b Hp2c]]].
    eexists. repeat constructor; eassumption.
  - sinvert Hp. specialize (IHHd H1). sinvert Hd'; sinvert Hp'.
    + specialize (IHHd _ _ H4 H2) as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
    + shelve.
  - sinvert Hp. specialize (IHHd H5 _ _ Hd' Hp') as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
  - sinvert Hp. eexists. repeat econstructor; eassumption.
  - sinvert Hp. specialize (IHHd H1 _ _ Hd' Hp') as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
  - sinvert Hp. specialize (IHHd H1 _ _ Hd' Hp') as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
  - sinvert Hp. eexists. repeat constructor; eassumption.
  - sinvert Hp. sinvert Hd'. sinvert Hp'. eexists. repeat constructor; eassumption.
  - sinvert Hp. specialize (IHHd H1). sinvert Hd'; sinvert Hp'.
    + specialize (IHHd _ _ H4 H2) as [p'' [Hp1 [Hp2 Hp3]]]. eexists. repeat constructor; eassumption.
    + shelve.
  - sinvert Hp. specialize (IHHd H4 _ _ Hd' Hp') as [p'' [Hp1 [Hp2 Hp3]]].
    eexists. repeat split; constructor; eassumption.
  Unshelve. Abort. (* Two lemmas left *)

Lemma pfx_cat_assoc_l : forall p q r s pq,
  PrefixConcat p q pq ->
  PrefixConcat pq r s ->
  exists qr, PrefixConcat p qr s /\ PrefixConcat q r qr.
Proof.
  intros p q r s pq Hl Hr. generalize dependent r. generalize dependent s. induction Hl; intros; (* sauto lq: on. *)
  (*
  - (* PfxEpsEmp *)
    sinvert Hr. eexists. repeat constructor.
  - (* PfxOneEmp *)
    sinvert H; sinvert Hr. { eexists. repeat constructor; assumption. } eexists. repeat constructor.
  - (* PfxOneFull *)
    sinvert Hr. eexists. repeat constructor.
  - (* PfxParPair *)
    sinvert Hr.
    specialize (IHHl1 _ _ H1) as [qr1 [Hqr1l Hqr1r]].
    specialize (IHHl2 _ _ H4) as [qr2 [Hqr2l Hqr2r]].
    eexists. repeat constructor; eassumption.
  - (* PfxCatFst *)
    sinvert Hr; specialize (IHHl _ _ H0) as [qr [Hqr1 Hqr2]]; eexists; repeat constructor; eassumption.
  - (* PfxCatBoth / PfxCatFst *)
    sinvert Hr. eexists. repeat constructor; assumption. (* never used the IH--odd *)
  - (* PfxCatBoth / PfxCatBoth *)
    sinvert Hr. specialize (IHHl _ _ H3) as [qr [Hqr1 Hqr2]]. eexists. repeat constructor; eassumption.
  - (* PfxSumEmp *)
    eexists. repeat constructor. assumption.
  - (* PfxSumInl *)
    sinvert Hr. specialize (IHHl _ _ H0) as [qr [Hqr1 Hqr2]]. eexists. repeat constructor; eassumption.
  - (* PfxSumInr *)
    sinvert Hr. specialize (IHHl _ _ H0) as [qr [Hqr1 Hqr2]]. eexists. repeat constructor; eassumption.
  - (* PfxStarEmp *)
    eexists. repeat constructor. assumption.
  - (* PfxStarDone *)
    sinvert Hr. eexists. repeat constructor.
  - (* PfxStarFirst *)
    sinvert Hr; specialize (IHHl _ _ H0) as [qr [Hqr1 Hqr2]]; eexists; repeat constructor; eassumption.
  - (* PfxStarRest / PfxCatBoth *)
    sinvert Hr. eexists. repeat constructor; assumption. (* Also didn't use the IH *)
  - (* PfxStarRest / PfxStarRest *)
    sinvert Hr. specialize (IHHl _ _ H3) as [qr [Hqr1 Hqr2]]. eexists. repeat constructor; eassumption.
  *)
  try (sinvert H; sinvert Hr; eexists; repeat constructor; assumption);
  try (eexists; repeat constructor; assumption); sinvert Hr; try specialize (IHHl _ _ H0) as [qr1 [Hqr1 Hqr2]];
  try specialize (IHHl _ _ H3) as [qr [Hqr1 Hqr2]]; try (eexists; repeat constructor; eassumption).
  specialize (IHHl1 _ _ H1) as [qr1 [Hqr1l Hqr1r]]. specialize (IHHl2 _ _ H4) as [qr2 [Hqr2l Hqr2r]].
  eexists. repeat constructor; eassumption.
Qed.

Lemma pfx_cat_assoc_r : forall p q r s qr,
  PrefixConcat p qr s ->
  PrefixConcat q r qr ->
  exists pq, PrefixConcat p q pq /\ PrefixConcat pq r s.
Proof.
  intros p q r s qr Hl Hr. generalize dependent r. generalize dependent q. induction Hl; intros.
  - (* PfxEpsEmp: p = PfxEpsEmp, qr = PfxEpsEmp
     * so we want to prove that there exists a pq s.t. EpsEmp . q ~ pq /\ pq . r ~ EpsEmp
     * obviously this should be EpsEmp, but the problem is we don't know q or r *)
    (* convenient fact I only realized after all cases: *) assert (A : r = PfxEpsEmp) by sauto lq: on. subst.
    (* so really the problem is forall q, exists pq, EpsEmp . q ~ pq /\ pq . EpsEmp ~ EpsEmp *)
    sinvert Hr.
    + (* q, r both PfxEpsEmp *) sauto lq: on.
    + (* q PfxOneEmp, r PfxEpsEmp *) sauto lq: on.
    + (* q PfxSumEmp, r PfxEpsEmp *)
      (* (no hypotheses) exists pq, PrefixConcat PfxEpsEmp PfxSumEmp pq /\ PrefixConcat pq PfxEpsEmp PfxEpsEmp *)
      Fail best time: 1000000000000000000. (* stops in < 1 second: probably actually false *) shelve.
    + (* q PfxStarEmp, r PfxEpsEmp *)
      Fail best time: 1000000000000000000. (* ditto ^^ *) shelve.
Abort.

Lemma oh_shit :
  ~exists pq, PrefixConcat PfxEpsEmp PfxSumEmp pq /\ PrefixConcat pq PfxEpsEmp PfxEpsEmp.
Proof. intros [pq [H1 H2]]. sinvert H1. Qed.

Lemma oh_fuck :
  ~exists pq, PrefixConcat PfxEpsEmp PfxSumEmp pq.
Proof. intros [pq H]. sinvert H. Qed.

(* TODO: here's the problem ^^^^^ *)

(*
(* This was incredibly difficult to state, and I'm not sure it's exactly what we want, but I'm confident.
 * Either way, we might need to package it more nicely for downstream use. *)
Lemma pfx_cat_assoc : forall p q r s,
  (exists pq, PrefixConcat p q pq /\ PrefixConcat pq r s) <->
  (exists qr, PrefixConcat p qr s /\ PrefixConcat q r qr).
Proof.
  split. { intros [pq [H1 H2]]. eapply pfx_cat_assoc_l; eassumption. } best use: pfx_cat_assoc_r.
Qed.
*)
