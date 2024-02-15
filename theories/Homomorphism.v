From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Derivative
  Inert
  Nullable
  Prefix
  Semantics
  SinkTerm
  Sets
  Terms
  Types
  PrefixConcat
  Subcontext
  SemSound
  Typing.

Definition P_hom g (e : term) (s : type) (i : inertness) eta (e' : term) p :=
  WFContext g ->
  EnvTyped eta g ->
  forall eta' eta'' e'' p' p'',
  Step eta' e' e'' p' ->
  PrefixConcat p p' p'' ->
  EnvConcat eta eta' eta'' ->
  Step eta'' e e'' p''
.

(* Theorem hom : forall g e s i eta e' p,
    Typed g e s i ->
    Step eta e e' p ->
    P_hom g e s i eta e' p
.
Proof.
apply (lex_ind P_hom); unfold P_hom in *; intros.
- eapply H2. eapply subtcontext_wf; eauto. eapply sub_preserves_env; eauto. eauto. eauto. eauto.
- best.
- sinvert H3; unfold EnvConcat in *; econstructor; qauto l: on use:pfx_cat_unique.
- sauto lq: on rew: off.
- sinvert H5. sinvert H7. sinvert H8. sinvert H6.
  + econstructor. hauto l: on. qauto l: on use:pfx_cat_maximal'.
  + sinvert H8. sinvert H6. econstructor; [ eauto | |]. eapply pfx_cat_maximal. eauto. best use:sound.
intros.
Admitted. *)