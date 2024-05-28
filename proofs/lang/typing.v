From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type expr Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make String_as_OT.

(* Map from string to pair of type and effect *)
Definition typing_context := M.t (ty * kind). 

Inductive ty_expr : typing_context -> expr -> ty -> kind -> Prop :=
| var_ty : forall Gamma t v, 
           M.find v Gamma = Some (t, KEmpty) ->
           ty_expr Gamma (EVar v) t KEmpty
| litint_ty : forall Gamma i,
              ty_expr Gamma (ELit (LitInt i)) (TCon tconInt) (get_kind_ty_const tconInt)
| litstring_ty : forall Gamma i,
              ty_expr Gamma (ELit (LitInt i)) (TCon tconString) (get_kind_ty_const tconString)
| lam_ty : forall Gamma x t k Gamma' e,
           M.add x (t, KEmpty) Gamma = Gamma' ->
           ty_expr Gamma' e t k ->
           ty_expr Gamma (ELam (EVar x) (t,k) e) t k.



