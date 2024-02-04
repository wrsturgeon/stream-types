From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  FV
  Hole
  Sets
  Subcontext
  Terms
  Inert
  Nullable
  Types.


Inductive Typed : context -> term -> type -> inertness -> Prop :=
  | TParR : forall G e1 e2 s t i1 i2 i3,
      Typed G e1 s i1 ->
      Typed G e2 t i2 ->
      i_ub i1 i2 i3 ->
      Typed G (e1, e2) (TyPar s t) i3
  | TParL : forall G x y z s t e r Gxsyt Gzst i,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyPar s t)) Gzst ->
      Typed Gxsyt e r i ->
      Typed Gzst (TmLetPar x y z e) r i
  | TCatR : forall G D e1 e2 s t i1 i2 i3,
      Typed G e1 s i1 ->
      Typed D e2 t i2 ->
      inert_guard (i1 = Inert /\ ~(Nullable s)) i3 ->
      Typed (CtxSemic G D) (e1; e2) (TyDot s t) i3
  | TCatL : forall G x y z s t e r Gxsyt Gzst i,
      x <> y ->
      ~fv G x ->
      ~fv G y ->
      Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
      Fill G (CtxHasTy z (TyDot s t)) Gzst ->
      Typed Gxsyt e r i ->
      Typed Gzst (TmLetCat t x y z e) r i
  | TEpsR : forall G i,
      Typed G TmSink TyEps i
  | TOneR : forall G,
      Typed G TmUnit TyOne Jumpy
  | TVar : forall G x s Gxs i,
      Fill G (CtxHasTy x s) Gxs ->
      Typed Gxs (TmVar x) s i
  | TSubCtx : forall G G' e s i,
      Subcontext G G' ->
      Typed G' e s i ->
      Typed G e s i
  | TLet : forall G D x e e' s t Gxs GD i,
      ~fv G x ->
      Typed D e s Inert ->
      Fill G (CtxHasTy x s) Gxs ->
      Fill G D GD ->
      Typed Gxs e' t i ->
      Typed GD (TmLet x e e') t i
   (* | TRec : forall g e g' eargs s, *)
      (* ArgsTyped g eargs g' -> *)
      (* Typed g e s *)

with ArgsTyped : context -> argsterm -> context -> Prop :=
  | T_ATmEmpty : forall g, ArgsTyped g ATmEmpty CtxEmpty
  | T_ATmSng : forall g e s x i,
      Typed g e s i ->
      ArgsTyped g (ATmSng e) (CtxHasTy x s)
  | T_ATmComma : forall g g1 g2 e1 e2,
      ArgsTyped g e1 g1 ->
      ArgsTyped g e2 g2 ->
      ArgsTyped g (ATmComma e1 e2) (CtxComma g1 g2)
  | T_ATmSemic : forall g1 g2 g1' g2' e1 e2,
      ArgsTyped g1 e1 g1' ->
      ArgsTyped g2 e2 g2' ->
      ArgsTyped (CtxSemic g1 g2) (ATmSemic e1 e2) (CtxSemic g1' g2')
.

Hint Constructors Typed : core.
Hint Constructors ArgsTyped : core.

Theorem typing_sub_inert : forall g e s i,
  Typed g e s i ->
  Typed g e s Jumpy
.
Proof.
intros.
induction H; intros.
- econstructor; sauto.
- econstructor; eauto.
- hfcrush.
- sfirstorder.
- hauto l: on.
- sauto lq: on.
- sfirstorder.
- best.
- best.
Qed.


(* TODO:
Theorem typed_wf_term : forall G x T,
  G |- x \in T ->
  WFTerm (fv G) x.
*)

Theorem typing_fv : forall G e s i,
  Typed G e s i ->
  forall x,
  fv e x ->
  fv G x.
Proof.
Admitted.
Hint Resolve typing_fv : core.

Theorem argstyping_fv : forall g e g',
  ArgsTyped g e g' ->
  forall x,
  fv e x ->
  fv g x.
Proof.
  intros.
  generalize dependent x.
  induction H; hauto l:on use:fv_term.
Qed.