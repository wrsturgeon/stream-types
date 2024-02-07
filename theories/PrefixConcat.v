From Hammer Require Import Tactics.
From LambdaST Require Import
  Derivative
  Prefix
  Environment
  FV
  Context
  Sets
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
      MaximalPrefix p ->
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
      MaximalPrefix p ->
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
  sfirstorder. sfirstorder.
Qed.
Hint Resolve pfx_cat_unique : core.



Theorem pfx_cat_maximal : forall p p' p'',
  PrefixConcat p p' p'' ->
  MaximalPrefix p \/ MaximalPrefix p' -> MaximalPrefix p''.
Proof.
  intros. induction H. 
  - sfirstorder.
  - sauto lq: on.
  - sfirstorder.
  - sauto lq: on rew: off.
  - sauto lq: on.
  - best.
  - best.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sfirstorder.
  - sauto lq: on.
  - sauto lq: on.
  - best.
Qed.
  
(* partial converse: if p . p' is maximal, than p' must be. *)
Theorem pfx_cat_maximal' : forall p p' p'',
  PrefixConcat p p' p'' ->
  MaximalPrefix p'' -> MaximalPrefix p'.
Proof.
  intros. generalize dependent H0. induction H. 
  - sfirstorder.
  - sauto lq: on.
  - sfirstorder.
  - sauto lq: on rew: off.
  - sauto lq: on.
  - best.
  - best.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sfirstorder.
  - sauto lq: on.
  - sauto lq: on.
  - sauto.
Qed.

Theorem pfx_cat_maximal'' : forall p,
  MaximalPrefix p ->
  exists p', PrefixConcat p p' p /\ EmptyPrefix p'.
Proof.
intros.
induction H; sauto lq: on.
Qed.

Theorem pfx_cat_maximal''' : forall p p' p'', MaximalPrefix p -> PrefixConcat p p' p'' -> p = p''.
Proof.
intros.
generalize dependent p'.
generalize dependent p''.
induction H.
- best.
- best.
- best.
- best.
- best.
- best.
- best.
- best.
Qed.

Theorem pfx_cat_empty : forall p p' p'',
  PrefixConcat p p' p'' ->
  EmptyPrefix p /\ EmptyPrefix p' <-> EmptyPrefix p''.
Proof.
intros.
induction H; sauto lq: on.
Qed.


(* Theorem B.21, part II *)
Theorem pfx_cat_exists_when_typed : forall p p' s dps,
  Derivative p s dps -> (* i.e., d_p(s) = `dps`. difficult to write in ASCII *)
  PrefixTyped p s ->
  PrefixTyped p' dps ->
  exists p'',
  PrefixConcat p p' p'' /\ (* from "such a p'' exists" *)
  PrefixTyped p'' s /\
  (forall dp'dps, Derivative p' dps dp'dps -> (* i.e. d_{p'}(d_p(s)) = `dp'dps` *)
    Derivative p'' s dp'dps).
Proof.
  intros.
  generalize dependent p'.
  generalize dependent dps.
  induction H0; intros.
  - sauto lq: on rew: off.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sinvert H.
    sinvert H1.
    + best.
    + edestruct IHPrefixTyped as [p00 [A [B C]]]; eauto.
      exists (PfxCatBoth p00 p2).
      split; try split.
     * hauto l: on.
     * sfirstorder use:pfx_cat_maximal.
     * sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sauto lq: on.
  - sinvert H.
    sinvert H1.
    + sauto lq: on.
    + edestruct IHPrefixTyped as [p00 [A [B C]]]; eauto.
      exists (PfxStarRest p00 p2).
      split; try split.
      * hauto l: on.
      * sfirstorder use:pfx_cat_maximal.
      * sauto lq: on.

  - sauto lq: on.
Qed.

(* TODO: prefix concatenation and derivatives,*)

Lemma pfx_cat_assoc : forall p q r s pq,
  PrefixConcat p q pq ->
  PrefixConcat pq r s ->
  exists qr, (PrefixConcat p qr s /\ PrefixConcat q r qr /\ (MaximalPrefix q -> q = qr)). (* had to strengthen this. *)
Proof.
  intros p q r s pq Hl Hr. generalize dependent r. generalize dependent s. induction Hl; intros. (* sauto lq: on. *)
  - best.
  - best.
  - best.
  - best.
  - best.
  - sinvert Hr. 
    edestruct (pfx_cat_maximal'' p'') as [U [V W]]; eauto.
    edestruct IHHl as [p0 [A [B C]]]; eauto.
    exists (PfxCatBoth p0 p'''0).
    split; try split.
    + best.
    + assert (p' = p0) by best use:pfx_cat_maximal'.
      destruct H.
      eapply PfxCatCatBoth.
      eauto.
      best use:pfx_cat_maximal'.
    + intros. sinvert H.
      best use:pfx_cat_maximal'''.
  - best.
  - best use:pfx_cat_maximal'''.
  - best.
  - best.
  - best use:pfx_cat_maximal'''.
  - best.
  - best.
  - sinvert Hr. 
    edestruct (pfx_cat_maximal'' p'') as [U [V W]]; eauto.
    edestruct IHHl as [p0 [A [B C]]]; eauto.
    exists (PfxCatBoth p0 p'''0).
    split; try split.
    + best.
    + assert (p' = p0) by best use:pfx_cat_maximal'.
      destruct H.
      eapply PfxCatCatBoth.
      eauto.
      best use:pfx_cat_maximal'.
    + intros. sinvert H.
      best use:pfx_cat_maximal'''.
  - best.
Qed.
Hint Resolve pfx_cat_assoc : core.

(* NOTE: Joe, this is what you said you needed last time--it was a pretty easy corollary of the above *)
Lemma pfx_cat_assoc_eq : forall p q r pq qr s1 s2,
  PrefixConcat p q pq ->
  PrefixConcat q r qr ->
  PrefixConcat pq r s1 ->
  PrefixConcat p qr s2 ->
  s1 = s2.
Proof.
  intros p q r pq qr s1 s2 Hpq Hqr Hs1 Hs2.
  assert (A := pfx_cat_assoc _ _ _ _ _ Hpq Hs1). destruct A as [qr' [H1 [H2 _]]].
  assert (A := pfx_cat_unique _ _ _ _ Hqr H2). clear H2. symmetry in A. subst.
  assert (A := pfx_cat_unique _ _ _ _ Hs2 H1). subst. reflexivity.
Qed.
Hint Resolve pfx_cat_assoc_eq : core.

(* TODO: environment concatenation, and the same.
 * Environment concat: n . n' ~ n'' if,
 * for all x in dom(n) and dom(n'),
 * n(x) . n'(x) ~ n''(x) *)

Definition EnvConcat (n : env) (n' : env) (n'' : env) : Prop :=
  (forall x p p', n x = Some p -> n' x = Some p' -> (exists p'', n'' x = Some p'' /\ PrefixConcat p p' p''))
  /\
  (forall x, n x = None \/ n' x = None -> n'' x = None) (* to ensure that n'' is unique, we need to restrict the domain. *)
.

Hint Unfold EnvConcat : core.

(* fuck it, i want this theorem to hold on the nose.  *)
Axiom functional_extensionality: forall {A B} (f g:A->B) , (forall x, f x = g x) -> f = g.


Theorem  env_cat_unique : forall n n' n1 n2,
  EnvConcat n n' n1 -> 
  EnvConcat n n' n2 -> 
  n1 = n2.
Proof.
  intros; eapply functional_extensionality; intros.
  unfold EnvConcat in *.
  destruct H as [A B].
  destruct H0 as [A' B'].
  remember (n x) as nx.
  remember (n' x) as n'x.
  destruct nx.
  - destruct n'x; [|sauto lq: on].
    hauto lq: on use:pfx_cat_unique.
  - sauto lq: on.
Qed.


(* TODO: will. *)
Theorem env_cat_exists_when_typed : forall eta eta' g g',
  ContextDerivative eta g g'->
  EnvTyped eta g ->
  EnvTyped eta' g' ->
  exists eta'',
  EnvConcat eta eta' eta'' /\
  EnvTyped eta'' g /\
  (forall g'', ContextDerivative eta' g' g'' ->
    ContextDerivative eta'' g g'').
Proof.
intros.
Admitted.

Theorem env_cat_maximal : forall s eta eta' eta'' g,
  EnvTyped eta g ->
  EnvConcat eta eta' eta'' ->
  Subset s (dom eta) ->
  Subset s (dom eta') ->
  Subset s (fv g) ->
  MaximalOn s eta \/ MaximalOn s eta' -> MaximalOn s eta''.
Proof.
intros.
unfold MaximalOn in *. unfold PropOn in *. unfold PropOnItem in *.
intros.
destruct H4.
+ assert (exists p, eta x = Some p) by best.
  edestruct H6 as [p].
  assert (MaximalPrefix p) by hauto l: on.
  assert (exists p', eta' x = Some p') by sfirstorder.
  edestruct H9 as [p'].
  assert (exists p'', eta'' x = Some p'') by sfirstorder.
  edestruct H11 as [p''].
Admitted.

Theorem env_cat_empty : forall s eta eta' eta'',
  EnvConcat eta eta' eta'' ->
  EmptyOn s eta /\ EmptyOn s eta' -> EmptyOn s eta''.
Proof.
intros.
Admitted.