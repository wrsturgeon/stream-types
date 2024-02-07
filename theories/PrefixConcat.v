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



(* TODO: will. previous version of this theorem was false because of par, we should only need one direction.
Also requires that the first prefix have *some type at all* so that you can pick that maximality condition out of the typing to prove (MaximalPrefix (PfxCatBoth p p')).
We might want to just bake MaximalPrefix p into the concat rule in case this becomes a problem when it comes time to use this theorem.
*)
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
  (* sauto lq: on rew: off. { repeat constructor. }
  - sinvert H. { tauto. } split. { constructor. } right. assumption.
  - split. { constructor. } left. assumption.
  - split; intros.
    + constructor; [apply IHPrefixConcat1 | apply IHPrefixConcat2];
      destruct H1; sinvert H1; try (left; assumption); right; assumption.
    + sinvert H1. apply IHPrefixConcat1 in H4. apply IHPrefixConcat2 in H5.
      destruct H4; destruct H5.
      * left. constructor; assumption.
      * admit. (* TODO: interesting mismatch *)
      * admit.
      * right. constructor; assumption.
  - split; intros. { destruct H0; sinvert H0. } sinvert H0.
  - split; intros.
    + constructor. { apply IHPrefixConcat. right. destruct H0; sinvert H0. assumption. }
      clear IHPrefixConcat. destruct H0; sinvert H0. assumption.
    + sinvert H0. apply IHPrefixConcat in H3 as [H3 | H3]; right; constructor; try assumption.
      admit.
  - split; intros.
    + constructor; [| apply IHPrefixConcat; destruct H0; [| right; assumption]; sinvert H0; left; assumption].
      destruct H0; [sinvert H0; assumption |]. admit.
    + sinvert H0. apply IHPrefixConcat in H4 as [H4 | H4]; [left; constructor | right]; assumption.
  - split; intros. { destruct H. { sinvert H. } assumption. } right. assumption.
  - split; intros. { constructor. apply IHPrefixConcat. sinvert H0; [sinvert H1; left | right]; assumption. }
    sinvert H0. apply IHPrefixConcat in H2 as [H2 | H2]; [left; constructor | right]; assumption.
  - split; intros. { constructor. apply IHPrefixConcat. sinvert H0; [sinvert H1; left | right]; assumption. }
    sinvert H0. apply IHPrefixConcat in H2 as [H2 | H2]; [left; constructor | right]; assumption.
  - split; intros. { destruct H. { sinvert H. } assumption. } right. assumption.
  - split; [| left]; constructor.
  - split; intros. { destruct H0; sinvert H0. } sinvert H0.
  - split; intros. { destruct H0; sinvert H0. constructor; [apply IHPrefixConcat; right |]; assumption. }
    sinvert H0. right. constructor; [| assumption]. admit.
  - split; intros.
    + destruct H0. { sinvert H0. constructor. { assumption. } apply IHPrefixConcat. left. assumption. }
      constructor; [| apply IHPrefixConcat; right; assumption]. admit.
    + sinvert H0. apply IHPrefixConcat in H4 as [H4 | H4]. { left. constructor; assumption. } right. assumption. *)
(* TODO: will: a few similar-looking cases are all either not true or not provable without induction/lemmas *)
(* TODO: will (joe note: looks like because it's not true! should only need one dir.)*)

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

Theorem pfx_cat_maximal'' : forall p, MaximalPrefix p -> exists p', PrefixConcat p p' p.
Proof.
intros.
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
Admitted.
  (* intros p p' s dps dp'dps Hd Hd' Hp Hp'. generalize dependent p'. generalize dependent dp'dps.
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
    eexists. repeat split; constructor; eassumption. *)
  (* Unshelve. Abort. TODO: two lemmas left *)

(* TODO: prefix concatenation and derivatives,*)

Lemma pfx_cat_assoc : forall p q r s pq,
  PrefixConcat p q pq ->
  PrefixConcat pq r s ->
  exists qr, (PrefixConcat p qr s /\ PrefixConcat q r qr /\ (MaximalPrefix q -> q = qr)).
Proof.
  intros p q r s pq Hl Hr. generalize dependent r. generalize dependent s. induction Hl; intros. (* sauto lq: on. *)
  - best.
  - best.
  - best.
  - best.
  - best.
  - sinvert Hr. 
    edestruct (pfx_cat_maximal'' p''); eauto.
    edestruct IHHl as [p0 [A [B C]]]; eauto.
    exists (PfxCatBoth p0 p'''0).
    split; try split.
    + best.
    + assert (p' = p0) by best use:pfx_cat_maximal'.
      destruct H0.
      eapply PfxCatCatBoth.
      eauto.
      best use:pfx_cat_maximal'.
    + intros. sinvert H0.
      best use:pfx_cat_maximal'''.
  - best.
  - best use:pfx_cat_maximal'''.
  - best.
  - best.
  - best use:pfx_cat_maximal'''.
  - best.
  - best.
  - sinvert Hr. 
    edestruct (pfx_cat_maximal'' p''); eauto.
    edestruct IHHl as [p0 [A [B C]]]; eauto.
    exists (PfxCatBoth p0 p'''0).
    split; try split.
    + best.
    + assert (p' = p0) by best use:pfx_cat_maximal'.
      destruct H0.
      eapply PfxCatCatBoth.
      eauto.
      best use:pfx_cat_maximal'.
    + intros. sinvert H0.
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