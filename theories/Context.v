From Coq Require Import
  List
  String.
From LambdaST Require Import
  Ident
  Terms
  Types.

Inductive context : Set :=
  | CtxEmpty
  | CtxHasTy (tm : term) (ty : type)
  | CtxComma (lhs rhs : context)
  | CtxSemic (lhs rhs : context)
  .

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

Theorem contains_is_find_repl_id : forall needle haystack,
  Contains needle haystack <-> FindReplace needle needle haystack haystack.
Proof. split; intros; induction H; constructor; assumption. Qed.

Fixpoint vars_in ctx :=
  match ctx with
  | CtxHasTy (TmVar x) _ => cons x nil
  | CtxHasTy _ _ | CtxEmpty => nil
  | CtxComma lhs rhs | CtxSemic lhs rhs => vars_in lhs ++ vars_in rhs
  end.
