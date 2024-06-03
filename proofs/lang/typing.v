From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type expr Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make String_as_OT.

(* Map from string to pair of type and effect *)
Definition typing_context := M.t (ty * kind). 

Inductive ty_expr : typing_context -> expr -> ty -> kind -> Prop :=
(* Variable evaluation does not produce any effect *)
| var_ty : forall Gamma t v, 
           M.find v Gamma = Some (t, KEmpty) ->
           ty_expr Gamma (EVar v) t KEmpty
(* An integer literal is of type int and effect kindStar (value types) *)
| litint_ty : forall Gamma i,
              ty_expr Gamma (ELit (LitInt i)) (TCon tconInt) (get_kind_ty_const tconInt)
(* An integer literal is of type int and effect kindStar (value types) *)
| litstring_ty : forall Gamma i,
              ty_expr Gamma (ELit (LitInt i)) (TCon tconString) (get_kind_ty_const tconString)
(* Lambda expression evaluates to a value, type is an arrow type and has no effect *)
| lam_ty : forall Gamma x t t' k Gamma' e,
           M.add x (t, KEmpty) Gamma = Gamma' ->
           ty_expr Gamma' e t' k ->
           ty_expr Gamma (ELam (EVar x) t e) (TFun t k t') KEmpty
(* Application produces the same effect as the function *)
| lapp_ty : forall Gamma t t' k e1 e2,
            ty_expr Gamma e1 (TFun t k t') k ->
            ty_expr Gamma e2 t k ->
            ty_expr Gamma (EApp e1 e2) t' k
| llet_ty : forall Gamma Gamma' x e1 e2 t1 t2 k,
            ty_expr Gamma e1 t1 KEmpty ->
            M.add x (t1, KEmpty) Gamma = Gamma' ->
            ty_expr Gamma' e2 t2 k ->
            ty_expr Gamma (ELet (EVar x) t1 e1 e2) t2 k.



