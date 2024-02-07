From Coq Require Import String.
From Hammer Require Import Tactics.
Require Import Coq.Program.Equality.
From LambdaST Require Import
  Context
  Environment
  FV
  Hole
  Nullable
  Prefix
  Semantics
  Sets
  SinkTerm
  Subcontext
  Terms
  Types
  Inert
  Typing.

Check Step_ind.
Check Typed_ind.

(*

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
        P n (TmLetCat t x y z e)
          (TmLet x (sink_tm p1) (Subst.subst_var e' z y)) p') ->
       (forall (eta : env) (x : string) (e1 e2 e1' e2' : term)
          (p p' : prefix),
        Step eta e1 e1' p ->
        P eta e1 e1' p ->
        Step (env_subst x p eta) e2 e2' p' ->
        P (env_subst x p eta) e2 e2' p' ->
        P eta (TmLet x e1 e2) (TmLet x e1' e2') p') ->
        ->
        ->
       (forall (eta eta' eta'' : env) (r : type) (z x y : string)
          (e1 e2 e' : term) (p p' : prefix),
        PrefixConcat.EnvConcat eta' eta eta'' ->
        eta'' z = Some (PfxSumInr p) ->
        Step (env_union eta (singleton_env y p)) e2 e' p' ->
        P (env_union eta (singleton_env y p)) e2 e' p' ->
        P eta (TmPlusCase eta' r z x e1 y e2) (Subst.subst_var e' z y) p') ->
       forall (e : env) (t t0 : term) (p : prefix),
       Step e t t0 p -> P e t t0 p
Typed_ind
	 : forall P : context -> term -> type -> inertness -> Prop,
       (forall (G : context) (e1 e2 : term) (s t : type)
          (i1 i2 i3 : inertness),
        Typed G e1 s i1 ->
        P G e1 s i1 ->
        Typed G e2 t i2 ->
        P G e2 t i2 -> i_ub i1 i2 i3 -> P G (TmComma e1 e2) (TyPar s t) i3) ->
       (forall (G : hole) (x y z : string) (s t : type) 
          (e : term) (r : type) (Gxsyt Gzst : context) 
          (i : inertness),
        x <> y ->
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
        Fill G (CtxHasTy z (s || t)) Gzst ->
        Typed Gxsyt e r i -> P Gxsyt e r i -> P Gzst (TmLetPar x y z e) r i) ->
       (forall (G D : context) (e1 e2 : term) (s t : type)
          (i1 i2 i3 : inertness),
        Typed G e1 s i1 ->
        P G e1 s i1 ->
        Typed D e2 t i2 ->
        P D e2 t i2 ->
        inert_guard (i1 = Inert /\ ~ Nullable s) i3 ->
        P (CtxSemic G D) (TmSemic e1 e2) (TyDot s t) i3) ->
       (forall (G : hole) (x y z : string) (s t : type) 
          (e : term) (r : type) (Gxsyt Gzst : context) 
          (i : inertness),
        x <> y ->
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
        Fill G (CtxHasTy z (s . t)) Gzst ->
        Typed Gxsyt e r i -> P Gxsyt e r i -> P Gzst (TmLetCat t x y z e) r i) ->
       (forall (G : context) (i : inertness), P G TmSink TyEps i) ->
       (forall G : context, P G TmUnit TyOne Jumpy) ->
       (forall (G : hole) (x : string) (s : type) 
          (Gxs : context) (i : inertness),
        Fill G (CtxHasTy x s) Gxs -> P Gxs (TmVar x) s i) ->
       (forall (G G' : context) (e : term) (s : type) (i : inertness),
        Subcontext G G' -> Typed G' e s i -> P G' e s i -> P G e s i) ->
       (forall (G : hole) (D Gxs : context) (x : string) 
          (e e' : term) (s t : type) (GD : context) 
          (i : inertness),
        ~ fv G x ->
        Typed D e s Inert ->
        P D e s Inert ->
        Fill G (CtxHasTy x s) Gxs ->
        Fill G D GD ->
        Typed Gxs e' t i -> P Gxs e' t i -> P GD (TmLet x e e') t i) ->
       (forall (G : context) (e : term) (s t : type) (i : inertness),
        Typed G e s i -> P G e s i -> P G (TmInl e) (TySum s t) Jumpy) ->
       (forall (G : context) (e : term) (s t : type) (i : inertness),
        Typed G e s i -> P G e s i -> P G (TmInr e) (TySum s t) Jumpy) ->
       (forall (G : hole) (x y z : string) (s t : type),
        type ->
        forall (Gz Gx Gy Gz' : context) (e1 e2 : term) 
          (eta : env) (r : type) (i i1 i2 : inertness),
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxHasTy z (s + t)) Gz ->
        Fill G (CtxHasTy x s) Gx ->
        Fill G (CtxHasTy y t) Gy ->
        EnvTyped eta Gz ->
        Derivative.ContextDerivative eta Gz Gz' ->
        Typed Gx e1 r i1 ->
        P Gx e1 r i1 ->
        Typed Gy e2 r i2 ->
        P Gy e2 r i2 -> P Gz' (TmPlusCase eta r z x e1 y e2) r i) ->
       forall (c : context) (t : term) (t0 : type) (i : inertness),
       Typed c t t0 i -> P c t t0 i

*)




Theorem lex_ind :
    forall P : context -> term -> type -> inertness -> env -> term -> prefix -> Prop,
    (* forall P' : context -> argsterm -> context -> env -> argsterm -> context -> env -> Prop, *)

    (forall (G G' : context) (e : term) (s : type) eta e' p i,
        Step eta e e' p ->
        Subcontext G G' -> Typed G' e s i -> P G' e s i eta e' p -> P G e s i eta e' p) ->
      
    (forall G n i, P G TmSink TyEps n i TmSink PfxEpsEmp) ->

    (forall G x s Gxs i n p,
      Fill G (CtxHasTy x s) Gxs ->
      n x = Some p ->
      P Gxs (TmVar x) s i n (TmVar x) p
    ) ->

    (forall G (n : env) (e1 e1' e2 e2' : term) (p1 p2 : prefix) s t i1 i2 i3,
        Step n e1 e1' p1 ->
        Typed G e1 s i1 ->

        Step n e2 e2' p2 ->
        Typed G e2 t i2 ->

        i_ub i1 i2 i3 ->

        forall IHe1 : P G e1 s i1 n e1' p1,
        forall IHe2 : P G e2 t i2 n e2' p2,

        P G (TmComma e1 e2) (TyPar s t) i3 n (TmComma e1' e2') (PfxParPair p1 p2)) ->

    (forall G D s t i1 i2 i3 (n : env) (e1 e1' e2 : term) (p : prefix),
        Typed G e1 s i1 ->
        Typed D e2 t i2 ->
        inert_guard (i1 = Inert /\ ~ Nullable s) i3 ->
        Step n e1 e1' p ->
        P G e1 s i1 n e1' p ->
        (~ MaximalPrefix p) ->
        P (CtxSemic G D) (TmSemic e1 e2) (TyDot s t) i3 n (TmSemic e1' e2) (PfxCatFst p)
      ) ->

    (forall G D s t i1 i2 i3 (n : env) (e1 e1' e2 e2' : term) (p1 p2 : prefix),
        Typed G e1 s i1 ->
        Typed D e2 t i2 ->
        inert_guard (i1 = Inert /\ ~ Nullable s) i3 ->
        Step n e1 e1' p1 ->
        P G e1 s i1 n e1' p1 ->
        MaximalPrefix p1 ->
        Step n e2 e2' p2 ->
        P D e2 t i2 n e2' p2 ->
        P (CtxSemic G D) (TmSemic e1 e2) (TyDot s t) i3 n e2' (PfxCatBoth p1 p2)) ->
    
    (forall G Gxsyt Gzst x y z s t r e n e' p1 p2 p' i,

        x <> y ->
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxComma (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
        Fill G (CtxHasTy z (TyPar s t)) Gzst ->
        Typed Gxsyt e r i -> 

        n z = Some (PfxParPair p1 p2) ->
        Step (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e e' p' ->

        forall IHe : P Gxsyt e r i (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e' p',

        P Gzst (TmLetPar x y z e) r i n (TmLetPar x y z e') p'
    ) ->

  (forall G Gxsyt Gzst s t r i (n : string -> option prefix) (x y z : string) (e e' : term) (p p' : prefix),
        x <> y ->
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
        Fill G (CtxHasTy z (TyDot s t)) Gzst ->

        Typed Gxsyt e r i ->
        forall IHe : P Gxsyt e r i (env_union n (env_union (singleton_env x p) (singleton_env y (emp t)))) e' p',

        n z = Some (PfxCatFst p) ->
        Step (env_union n (env_union (singleton_env x p) (singleton_env y (emp t)))) e e' p' ->
        
        P Gzst (TmLetCat t x y z e) r i n (TmLetCat t x y z e') p'
  ) ->

  (forall G Gxsyt Gzst s t r i (n : string -> option prefix) (x y z : string) (e e' : term) (p1 p2 p' : prefix),
        x <> y ->
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxSemic (CtxHasTy x s) (CtxHasTy y t)) Gxsyt ->
        Fill G (CtxHasTy z (TyDot s t)) Gzst ->

        Typed Gxsyt e r i ->
        forall IHe : P Gxsyt e r i (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e' p',

        n z = Some (PfxCatBoth p1 p2) ->
        Step (env_union n (env_union (singleton_env x p1) (singleton_env y p2))) e e' p' ->
        
        P Gzst (TmLetCat t x y z e) r i n (TmLet x (sink_tm p1) (Subst.subst_var e' z y)) p'
  ) ->

  (forall G s t Gz Gx Gy Gz' i1 i2 i (eta eta' eta'' : env) (r : type) (z x y : string) (e1 e2 : term),
        PrefixConcat.EnvConcat eta' eta eta'' ->
        eta'' z = Some PfxSumEmp ->

        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxHasTy z (TySum s t)) Gz ->
        Fill G (CtxHasTy x s) Gx ->
        Fill G (CtxHasTy y t) Gy ->
        EnvTyped eta' Gz ->
        Derivative.ContextDerivative eta' Gz Gz' ->
        Typed Gx e1 r i1 ->
        Typed Gy e2 r i2 ->
        inert_guard (eta' z = Some PfxSumEmp) i ->

        P Gz' (TmPlusCase eta' r z x e1 y e2) r i eta (TmPlusCase eta'' r z x e1 y e2) (emp r)
  ) ->

  (forall G Gx Gy Gz Gz' s t i1 i2 i (eta eta' eta'' : env) (r : type) (z x y : string) (e1 e2 e' : term) (p p' : prefix),
        PrefixConcat.EnvConcat eta' eta eta'' ->
        eta'' z = Some (PfxSumInl p) ->
        Step (env_union eta'' (singleton_env x p)) e1 e' p' ->

        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxHasTy z (TySum s t)) Gz ->
        Fill G (CtxHasTy x s) Gx ->
        Fill G (CtxHasTy y t) Gy ->
        EnvTyped eta' Gz ->
        Derivative.ContextDerivative eta' Gz Gz' ->
        Typed Gx e1 r i1 ->
        Typed Gy e2 r i2 ->
        inert_guard (eta' z = Some PfxSumEmp) i ->
        
        P Gx e1 r i1 (env_union eta'' (singleton_env x p)) e' p' ->
        P Gz' (TmPlusCase eta' r z x e1 y e2) r i eta (Subst.subst_var e' z x) p'
  ) ->

 (* (forall (G : hole) (x y z : string) (s t : type), type -> forall (Gz Gx Gy Gz' : context) (e1 e2 : term)  (eta : env) (r : type) (i i1 i2 : inertness),
        ~ fv G x ->
        ~ fv G y ->
        Fill G (CtxHasTy z (s + t)) Gz ->
        Fill G (CtxHasTy x s) Gx ->
        Fill G (CtxHasTy y t) Gy ->
        EnvTyped eta Gz ->
        Derivative.ContextDerivative eta Gz Gz' ->
        Typed Gx e1 r i1 ->
        P Gx e1 r i1 ->
        Typed Gy e2 r i2 ->
        P Gy e2 r i2 -> P Gz' (TmPlusCase eta r z x e1 y e2) r i) 
 *)

(* g_in (e : argsterm) g_out eta_in (e' : argsterm) g_out' eta_out := *)
    (forall G e s i eta e' p, Typed G e s i -> Step eta e e' p -> P G e s i eta e' p).
    (* (forall g_in args g_out eta_in args' eta_out g_out', ArgsTyped g_in args g_out -> ArgsStep eta_in g_out args args g_out' eta_out -> *)
      (* P' g_in args g_out eta_in args' g_out' eta_out). *)
Proof.
  intros.
  generalize dependent G.
  generalize dependent s.
  generalize dependent i.
  induction H11; intros s G i H00.
  - admit.
  - admit.
  - admit.
  - admit.
  - dependent induction H00.
    + hauto l: on.
    + sfirstorder.
  - admit.
  - admit.
  - dependent induction H00.
    + sauto lq: on rew: off.
    + eapply H; eauto.
  - admit.
  - admit.
  - dependent induction H00.
    + eapply H; eauto.
    + best.
  - dependent induction H00.
    + eapply H; eauto.
    + sauto lq: on rew: off.
  (* - dependent induction H00; sfirstorder.
  - admit.
  - dependent induction H00; sfirstorder.
  - dependent induction H00; sfirstorder.
  - admit.
  - admit.
  - dependent induction H00.
    + sauto lq: on rew: off.
    + eapply H; sfirstorder.
  - admit.
  - admit.
  - admit. *)
Admitted.
