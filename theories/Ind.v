From Coq Require Import String.
From Hammer Require Import Tactics.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Prefix
  Semantics
  SinkTerm
  Sets
  Terms
  Types
  Typing
  Nullable
  Inertness
  .

Check Typed_ind.
Check Step_ind.

(* Typed_ind
	 : forall P : context -> term -> type -> Prop,
       (forall (G : context) (e1 e2 : term) (s t : type),
        Typed G e1 s ->
        P G e1 s ->
        Typed G e2 t -> P G e2 t -> P G (TmComma e1 e2) (TyPar s t)) ->
       (forall (G : hole) (x y z : string) (s t : type) 
          (e : term) (r : type) (Gxsyt Gzst : context),
        x <> y ->
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
        Fill G (CtxHasTy z (s || t)) Gzst ->
        Typed Gxsyt e r -> P Gxsyt e r -> P Gzst (TmLetPar x y z e) r) ->
       (forall (G D : context) (e1 e2 : term) (s t : type),
        Typed G e1 s ->
        P G e1 s ->
        Typed D e2 t ->
        P D e2 t -> P (CtxSemic G D) (TmSemic e1 e2) (TyDot s t)) ->
       (forall (G : hole) (x y z : string) (s t : type) 
          (e : term) (r : type) (Gxsyt Gzst : context),
        x <> y ->
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
        Fill G (CtxHasTy z (s . t)) Gzst ->
        Typed Gxsyt e r -> P Gxsyt e r -> P Gzst (TmLetCat t x y z e) r) ->
       (forall G : context, P G TmSink TyEps) ->
       (forall G : context, P G TmUnit TyOne) ->
       (forall (G : hole) (x : string) (s : type) (Gxs : context),
        Fill G (CtxHasTy x s) Gxs -> P Gxs (TmVar x) s) ->
       (forall (G G' : context) (e : term) (s : type),
        CtxLEq G G' -> Typed G' e s -> P G' e s -> P G e s) ->
       (forall (G : hole) (D : context) (x : string) 
          (e e' : term) (s t : type) (Gxs GD : context),
        ~ fv G x ->
        Typed D e s ->
        P D e s ->
        Fill G (CtxHasTy x s) Gxs ->
        Fill G D GD -> Typed Gxs e' t -> P Gxs e' t -> P GD (TmLet x e e') t) ->
       (forall (G : hole) (x : string) (s t : type) 
          (e : term) (Ge Gxs : context),
        Fill G CtxEmpty Ge ->
        Fill G (CtxHasTy x s) Gxs ->
        Typed Ge e t -> P Ge e t -> P Gxs (TmDrop x e) t) ->
       forall (c : context) (t : term) (t0 : type), Typed c t t0 -> P c t t0
Step_ind
	 : forall P : env -> term -> term -> prefix -> Prop,
       (forall n : env, P n TmSink TmSink PfxEpsEmp) ->
       (forall n : env, P n TmUnit TmSink PfxOneFull) ->
       (forall (n : string -> option prefix) (x : string) (p : prefix),
        n x = Some p -> P n (TmVar x) (TmVar x) p) ->
       (forall (n : env) (e1 e1' e2 e2' : term) (p1 p2 : prefix),
        Step n e1 e1' p1 ->
        P n e1 e1' p1 ->
        Step n e2 e2' p2 ->
        P n e2 e2' p2 ->
        P n (TmComma e1 e2) (TmComma e1' e2') (PfxParPair p1 p2)) ->
       (forall (n : env) (e1 e1' e2 : term) (p : prefix),
        Step n e1 e1' p ->
        P n e1 e1' p ->
        ~ MaximalPrefix p ->
        P n (TmSemic e1 e2) (TmSemic e1' e2) (PfxCatFst p)) ->
       (forall (n : env) (e1 e1' e2 e2' : term) (p1 p2 : prefix),
        Step n e1 e1' p1 ->
        P n e1 e1' p1 ->
        MaximalPrefix p1 ->
        Step n e2 e2' p2 ->
        P n e2 e2' p2 -> P n (TmSemic e1 e2) e2' (PfxCatBoth p1 p2)) ->
       (forall (n : string -> option prefix) (x y z : string) 
          (e e' : term) (p1 p2 p' : prefix),
        n z = Some (PfxParPair p1 p2) ->
        Step
          (env_union n (env_union (singleton_env x p1) (singleton_env y p2)))
          e e' p' ->
        P (env_union n (env_union (singleton_env x p1) (singleton_env y p2)))
          e e' p' -> P n (TmLetPar x y z e) (TmLetPar x y z e') p') ->
       (forall (t : type) (n : string -> option prefix) 
          (x y z : string) (e e' : term) (p p' : prefix),
        n z = Some (PfxCatFst p) ->
        Step
          (env_union n
             (env_union (singleton_env x p) (singleton_env y (emp t)))) e e'
          p' ->
        P
          (env_union n
             (env_union (singleton_env x p) (singleton_env y (emp t)))) e e'
          p' -> P n (TmLetCat t x y z e) (TmLetCat t x y z e') p') ->
       (forall (t : type) (n : string -> option prefix) 
          (x y z : string) (e e' : term) (p1 p2 p' : prefix),
        n z = Some (PfxCatBoth p1 p2) ->
        Step
          (env_union n (env_union (singleton_env x p1) (singleton_env y p2)))
          e e' p' ->
        P (env_union n (env_union (singleton_env x p1) (singleton_env y p2)))
          e e' p' ->
        P n (TmLetCat t x y z e) (TmLet x (sink_tm p1) (subst_var e z y)) p') ->
       (forall (eta : env) (x : string) (e1 e2 e1' e2' : term)
          (p p' : prefix),
        Step eta e1 e1' p ->
        P eta e1 e1' p ->
        Step (env_subst x p eta) e2 e2' p' ->
        P (env_subst x p eta) e2 e2' p' ->
        P eta (TmLet x e1 e2) (TmLet x e1' e2') p') ->
       (forall (eta : env) (x : string) (e e' : term) (p : prefix),
        Step (env_drop eta x) e e' p ->
        P (env_drop eta x) e e' p -> P eta (TmDrop x e) (TmDrop x e') p) ->
       forall (e : env) (t t0 : term) (p : prefix),
       Step e t t0 p -> P e t t0 p *)

Theorem lex_ind :
    forall P : context -> term -> type -> env -> term -> prefix -> Prop,



    (forall G e s eta e' p, P G e s eta e' p).
Admitted.