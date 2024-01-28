From Coq Require Import
  Bool
  String.

Class Eqb (T : Type) := {
  eqb : T -> T -> bool;
  eq_dec : forall a b : T, {a = b} + {a <> b};
  eqb_spec : forall a b : T, reflect (a = b) (eqb a b);
}.

Instance eqb_string : Eqb string := { eqb := String.eqb; eq_dec := string_dec; eqb_spec := String.eqb_spec; }.
Instance eqb_bool : Eqb bool := { eqb := Bool.eqb; eq_dec := bool_dec; eqb_spec := Bool.eqb_spec; }.
