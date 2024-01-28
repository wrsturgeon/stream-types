Definition set T := T -> Prop.
Arguments set/ T.
Hint Unfold set : core.

Definition empty_set {T} : set T := fun _ => False.
Arguments empty_set {T}/ x.
Hint Unfold empty_set : core.

Definition singleton_set {T} e : set T := fun x => e = x.
Arguments singleton_set {T} e/ x.
Hint Unfold singleton_set : core.

Definition set_union {T} (a b : set T) : set T := fun x => a x \/ b x.
Arguments set_union {T} a b/ x.
Hint Unfold set_union : core.

Definition set_intersection {T} (a b : set T) : set T := fun x => a x /\ b x.
Arguments set_intersection {T} a b/ x.
Hint Unfold set_union : core.

Definition set_minus {T} (a b : set T) : set T := fun x => a x /\ ~b x.
Arguments set_minus {T} a b/ x.
Hint Unfold set_minus : core.

Definition DisjointSets {T} (a b : set T) : Prop := forall x,
  (a x -> ~b x) /\ (b x -> ~a x).
Arguments DisjointSets {T} a b/.
Hint Unfold DisjointSets : core.

(* Argument order chosen for currying: `(SubsetOf a)` can be read out loud *)
Definition SubsetOf {T} (big little : set T) : Prop := forall x,
  little x -> big x.
Arguments SubsetOf {T} big little.
Hint Unfold SubsetOf : core.

Definition SetEq {T} (a b : set T) : Prop := forall x,
  a x <-> b x.
Arguments SetEq {T} a b/.
Hint Unfold SetEq : core.

Definition SetProp {T} (P : T -> Prop) (s : set T) : Prop := forall x, s x -> P x.
Arguments SetProp {T} P s/.
Hint Unfold SetProp : core.

Example set_prop_123 :
  let s123 := set_union (set_union (singleton_set 1) (singleton_set 2)) (singleton_set 3) in
  SetProp (fun x => x < 10) s123.
Proof.
  cbn. (* key part is destructing the set hypothesis here: *) intros x [[H1 | H2] | H3];
  (* and each resulting case is trivial: *) subst; repeat constructor.
Qed.

(* Analogous to `Forall_impl` *)
Lemma set_prop_impl : forall {T} P' P s,
  @SetProp T P s ->
  (forall t, P t -> P' t) ->
  SetProp P' s.
Proof. auto. Qed.

(* Analogous to `incl_Forall` *)
Lemma set_prop_incl : forall {T} P big little,
  @SetProp T P big ->
  SubsetOf big little ->
  SetProp P little.
Proof. auto. Qed.