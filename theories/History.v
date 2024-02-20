(* From Coq Require Import String. *)
From Coq Require Import
  List
  Program.Equality
  .
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Prefix
  Types.

Inductive histval : Set :=
  | HVUnit
  | HVPair : histval -> histval -> histval
  | HVInl : histval -> histval
  | HVInr : histval -> histval
  | HVNil : histval
  | HVCons : histval -> histval -> histval
.

Inductive histty : Set :=
  | HTUnit
  | HTProd (lhs rhs : histty)
  | HTSum (lhs rhs : histty)
  | HTList (t : histty)
  .
Hint Constructors histty : core.

Inductive HistValTyped : histval -> histty -> Prop :=
| HVTUnit : HistValTyped HVUnit HTUnit
| HVTPair : forall v1 v2 t1 t2,
    HistValTyped v1 t1 ->
    HistValTyped v2 t2 ->
    HistValTyped (HVPair v1 v2) (HTProd t1 t2)
| HVTInl : forall v t1 t2,
    HistValTyped v t1 ->
    HistValTyped (HVInl v) (HTSum t1 t2)
| HVTInr : forall v t1 t2,
    HistValTyped v t2 ->
    HistValTyped (HVInr v) (HTSum t1 t2)
| HVTNil : forall t, HistValTyped HVNil (HTList t)
| HVTCons : forall t v1 v2,
    HistValTyped v1 t ->
    HistValTyped v2 (HTList t) ->
    HistValTyped (HVCons v1 v2) (HTList t)
.

Inductive HistValAllTyped : list histval -> list histty -> Prop :=
| HVATnil : HistValAllTyped nil nil
| HVATcons : forall v vs t ts, HistValTyped v t -> HistValAllTyped vs ts -> HistValAllTyped (cons v vs) (cons t ts)
.


Fixpoint flatten_type t :=
  match t with
  | TyOne
  | TyEps => HTUnit
  | TyDot lhs rhs
  | TyPar lhs rhs =>
      HTProd (flatten_type lhs) (flatten_type rhs)
  | TySum lhs rhs =>
      HTSum (flatten_type lhs) (flatten_type rhs)
  | TyStar t =>
      HTList (flatten_type t)
  end.

Definition histctx := list histty.
Hint Unfold histctx : core.

Inductive PrefixFlatten : prefix -> histval -> Prop :=
| PLEps : PrefixFlatten PfxEpsEmp HVUnit
| PLOne : PrefixFlatten PfxOneFull HVUnit
| PLParPair : forall p1 p2 v1 v2,
    PrefixFlatten p1 v1 ->
    PrefixFlatten p2 v2 ->
    PrefixFlatten (PfxParPair p1 p2) (HVPair v1 v2)
| PLCatBoth : forall p1 p2 v1 v2,
    PrefixFlatten p1 v1 ->
    PrefixFlatten p2 v2 ->
    PrefixFlatten (PfxCatBoth p1 p2) (HVPair v1 v2)
| PLInl : forall p v,
    PrefixFlatten p v ->
    PrefixFlatten (PfxSumInl p) (HVInl v)
| PLInr : forall p v,
    PrefixFlatten p v ->
    PrefixFlatten (PfxSumInr p) (HVInr v)
| PLDone : PrefixFlatten PfxStarDone HVNil
| PLCons : forall p p' v v',
    PrefixFlatten p v ->
    PrefixFlatten p' v' ->
    PrefixFlatten (PfxStarRest p p') (HVCons v v')
.

Theorem prefix_flatten_det : forall p v v',
  PrefixFlatten p v ->
  PrefixFlatten p v' ->
  v = v'.
Proof.
intros.
generalize dependent v'.
induction H; intros; sauto lq: on.
Qed.

(* TODO: will *)
Theorem maximal_prefix_flatten : forall p s,
  PrefixTyped p s ->
  MaximalPrefix p ->
  exists v, PrefixFlatten p v /\ HistValTyped v (flatten_type s).
Proof.
intros.
generalize dependent H0.
induction H; intros.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto q: on.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto lq: on.
- sauto.
Qed.

(* TODO: will *)
Theorem maximal_prefix_flatten' : forall p s v,
  PrefixTyped p s ->
  MaximalPrefix p ->
  PrefixFlatten p v ->
  HistValTyped v (flatten_type s).
Proof.
  intros.
  generalize dependent v.
  generalize dependent H0.
  induction H; sauto lq: on.
Qed.

Inductive HistValLift : type -> histval -> prefix -> Prop :=
| PFEps : HistValLift eps HVUnit PfxEpsEmp 
| PFOne : HistValLift TyOne HVUnit PfxOneFull 
| PFParPair : forall s t p1 p2 v1 v2,
    HistValLift s v1 p1 ->
    HistValLift t v2 p2 ->
    HistValLift (TyPar s t) (HVPair v1 v2) (PfxParPair p1 p2)
| PFCatBoth : forall s t p1 p2 v1 v2,
    HistValLift s v1 p1 ->
    HistValLift t v2 p2 ->
    HistValLift (TyDot s t) (HVPair v1 v2) (PfxCatBoth p1 p2)
| PFInl : forall s t p v,
    HistValLift s v p -> 
    HistValLift (TySum s t) (HVInl v) (PfxSumInl p)
| PFInr : forall s t p v,
    HistValLift t v p ->
    HistValLift (TySum s t) (HVInr v) (PfxSumInr p)
| PFDone : forall s, HistValLift (TyStar s) HVNil PfxStarDone 
| PFCons : forall s p p' v v',
    HistValLift s v p ->
    HistValLift (TyStar s) v' p' ->
    HistValLift (TyStar s) (HVCons v v') (PfxStarRest p p')
.

Theorem histval_lift_det : forall s v p p',
  HistValLift s v p ->
  HistValLift s v p' ->
  p = p'.
Proof.
intros.
generalize dependent p'.
induction H; sauto lq: on rew: off.
Qed.

(* TODO: will *)
Theorem histval_lift_fun : forall s v,
  HistValTyped v (flatten_type s) ->
  exists p, HistValLift s v p /\ MaximalPrefix p /\ PrefixTyped p s.
Proof.
intros.
dependent induction H.
- destruct s; cbn in *; sinvert x; eexists; sfirstorder.
- destruct s; cbn in *; sinvert x; sauto lq: on.
- destruct s; cbn in *; sinvert x; sauto lq: on.
- destruct s; cbn in *; sinvert x; sauto lq: on.
- destruct s; cbn in *; sinvert x; sauto lq: on.
- destruct s; cbn in *; try scongruence. 
  edestruct (IHHistValTyped1 s); [scongruence |].
  edestruct (IHHistValTyped2 (TyStar s)); [scongruence |].
  sauto lq: on.
Qed.

Definition histtm : Set.
Admitted.

Definition histargs := list histtm.

Definition HistTyped : histctx -> histtm -> histty -> Prop.
Admitted.

Definition HistStep : histtm -> histval -> Prop.
Admitted.

(* don't prove, opaque. *)
Theorem HistStep_sound : forall hp t v,
  HistTyped nil hp t ->
  HistStep hp v ->
  HistValTyped v t.
Proof.
Admitted.

Inductive HistArgsTyped : histctx -> histargs -> histctx -> Prop :=
| HATnil : forall o, HistArgsTyped o nil nil
| HATcons : forall e es t o o',
    HistTyped o e t ->
    HistArgsTyped o es o' ->
    HistArgsTyped o (cons e es) (cons t o')
.

Inductive HistArgsStep : histargs -> list histval -> Prop :=
| HASnil : HistArgsStep nil nil
| HAScons : forall e es v vs, HistStep e v -> HistArgsStep es vs -> HistArgsStep (cons e es) (cons v vs)
.

(* TODO: will *)
Theorem HistArgsStep_sound : forall args ts vs,
  HistArgsTyped nil args ts ->
  HistArgsStep args vs ->
  HistValAllTyped vs ts.
Proof.
  intros.
  generalize dependent vs.
  dependent induction H; intros; sauto l: on use:HistStep_sound.
Qed.

Definition histval_subst_hist (v : histval) (n : nat) (e : histtm) : histtm.
Admitted.

Fixpoint histval_subst_all_hist (vs : list histval) (e : histtm) : histtm :=
  match vs with
    nil => e
  | cons v vs' => histval_subst_all_hist vs' (histval_subst_hist v 0 e)
  end.

Fixpoint histval_subst_histargs (v : histval) (n : nat) (e : histargs) : histargs :=
  match e with
    nil => nil
  | cons e es => cons (histval_subst_hist v n e) (histval_subst_histargs v n es)
  end.

Theorem histval_subst_hist_thm : forall t ts ts' e t' v n,
  HistTyped (app ts (cons t ts')) e t' ->
  length ts = n ->
  HistValTyped v t ->
  HistTyped (app ts ts') (histval_subst_hist v n e) t'.
Proof.
Admitted.

(* TODO: will *)
Theorem histval_subst_histargs_thm : forall t ts es ts' ts0' v n,
  HistArgsTyped (app ts (cons t ts')) es ts0' ->
  length ts = n ->
  HistValTyped v t ->
  HistArgsTyped (app ts ts') (histval_subst_histargs v n es) ts0'.
Proof.
intros.
generalize dependent n.
generalize dependent v.
dependent induction H; intros.
- sfirstorder.
- hauto l: on use:histval_subst_hist_thm.
Qed.

