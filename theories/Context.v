From Coq Require Import
  List
  String.
From LambdaST Require Import
  Ident
  Invert
  Terms
  Types.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (id : ident) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .

Variant SameHead : context -> context -> Prop :=
  | SameHeadId : forall ctx, SameHead ctx ctx
  | SameHeadCommaL : forall ll lr r, SameHead (CtxComma ll r) (CtxComma lr r)
  | SameHeadCommaR : forall l rl rr, SameHead (CtxComma l rl) (CtxComma l rr)
  | SameHeadSemicL : forall ll lr r, SameHead (CtxSemic ll r) (CtxSemic lr r)
  | SameHeadSemicR : forall l rl rr, SameHead (CtxSemic l rl) (CtxSemic l rr)
  .

Inductive hole : Set :=
  | HoleRoot
  | HoleCommaL (lhs : hole) (rhs : context)
  | HoleCommaR (lhs : context) (rhs : hole)
  | HoleSemicL (lhs : hole) (rhs : context)
  | HoleSemicR (lhs : context) (rhs : hole)
  .

Fixpoint fill hole ctx :=
  match hole with
  | HoleRoot => ctx
  | HoleCommaL lhs rhs => CtxComma (fill lhs ctx) rhs
  | HoleCommaR lhs rhs => CtxComma lhs (fill rhs ctx)
  | HoleSemicL lhs rhs => CtxSemic (fill lhs ctx) rhs
  | HoleSemicR lhs rhs => CtxSemic lhs (fill rhs ctx)
  end.

Notation "G ( H )" := (fill G H) (at level 190).

Inductive FindReplace : context -> context -> context -> context -> Prop :=
  | FindReplExact : forall a b,
      FindReplace a b a b
  | FindReplCommaL : forall a b la lb r,
      FindReplace a b la lb ->
      FindReplace a b (CtxComma la r) (CtxComma lb r)
  | FindReplCommaR : forall a b l ra rb,
      FindReplace a b ra rb ->
      FindReplace a b (CtxComma l ra) (CtxComma l rb)
  | FindReplSemicL : forall a b la lb r,
      FindReplace a b la lb ->
      FindReplace a b (CtxSemic la r) (CtxSemic lb r)
  | FindReplSemicR : forall a b l ra rb,
      FindReplace a b ra rb ->
      FindReplace a b (CtxSemic l ra) (CtxSemic l rb)
  .

Ltac find_repl :=
  intros;
  try solve [apply FindReplExact];
  try solve [apply FindReplCommaL; find_repl];
  try solve [apply FindReplCommaR; find_repl];
  try solve [apply FindReplSemicL; find_repl];
  try solve [apply FindReplSemicR; find_repl];
  fail.

Example find_repl_semic_r : forall a b c,
  FindReplace a b (CtxSemic c a) (CtxSemic c b).
Proof.
  find_repl.
Qed.

(*
Inductive Contains : context -> context -> Prop :=
  | ContainsExact : forall c,
      Contains c c
  | ContainsCommaL : forall c lhs rhs,
      Contains c lhs ->
      Contains c (CtxComma lhs rhs)
  | ContainsCommaR : forall c lhs rhs,
      Contains c rhs ->
      Contains c (CtxComma lhs rhs)
  | ContainsSemicL : forall c lhs rhs,
      Contains c lhs ->
      Contains c (CtxSemic lhs rhs)
  | ContainsSemicR : forall c lhs rhs,
      Contains c rhs ->
      Contains c (CtxSemic lhs rhs)
  .

Ltac contains :=
  intros;
  try solve [apply ContainsExact];
  try solve [apply ContainsCommaL; contains];
  try solve [apply ContainsCommaR; contains];
  try solve [apply ContainsSemicL; contains];
  try solve [apply ContainsSemicR; contains];
  fail.

Example contains_semic_r : forall lhs rhs,
  Contains rhs (CtxSemic lhs rhs).
Proof. contains. Qed.

Theorem contains_is_find_repl_id : forall needle haystack,
  Contains needle haystack <-> FindReplace needle needle haystack haystack.
Proof. split; intros; induction H; constructor; assumption. Qed.
*)

Fixpoint vars_in ctx : list ident :=
  match ctx with
  | CtxEmpty => nil
  | CtxHasTy x _ => cons x nil
  | CtxComma lhs rhs | CtxSemic lhs rhs => vars_in lhs ++ vars_in rhs
  end.

Theorem hole_to_find_repl : forall G A B,
  FindReplace A B (fill G A) (fill G B).
Proof. induction G; intros; constructor; apply IHG. Qed.

Theorem hole_repr_eq : forall G A B GA GB,
  (~SameHead A B) ->
  ((fill G A = GA /\ fill G B = GB) <-> (FindReplace A B GA GB)).
Proof.
  induction G; intros.
  - (* Hole at the root. *)
    simpl. split.
    + (* Fixpoint -> Inductive *) intros [HA HB]. invert HA. constructor.
    + (* Inductive -> Fixpoint *) intros Hc. Print FindReplace. induction Hc.
      * split; reflexivity.
      * apply IHHc in H. invert H. split. fail.
