From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type expr Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.

Module M := FMapAVL.Make String_as_OT.

(* Map from string to pair of type and effect *)
Definition typing_context {e : Type} := M.t (@ty e). 

Inductive ty_expr {e : Type} : typing_context -> @expr e -> @ty e -> kind e -> Prop :=
(* Variable evaluation does not produce any effect *)
| var_ty : forall (Gamma : typing_context) t v, 
           M.find v Gamma = Some t ->
           ty_expr Gamma (EVar v) t (@KEmpty e)
(* An integer literal is of type int and effect kindStar (value types) *)
| litint_ty : forall Gamma i,
              ty_expr Gamma (ELit (LitInt i)) (TCon (TyCon tint)) (@KEmpty e)
| litstring_ty : forall Gamma i,
              ty_expr Gamma (ELit (LitString i)) (TCon (TyCon tstring)) (@KEmpty e)
(* Lambda expression evaluates to a value, type is an arrow type and has no effect 
   The rule assumes only one argument as of now *)
| lam_ty : forall Gamma x t t' k Gamma' be,
           M.add x t Gamma = Gamma' ->
           ty_expr Gamma' be t' k ->
           ty_expr Gamma (ELam (EVar x) t be) (TFun t k t') (@KEmpty e)
(* Application produces the same effect as the function *)
| app_ty : forall Gamma t t' k e1 e2,
            ty_expr Gamma e1 (TFun t k t') k ->
            ty_expr Gamma e2 t k ->
            ty_expr Gamma (EApp e1 e2) t' k
| let_ty : forall Gamma Gamma' x e1 e2 t1 t2 k,
            ty_expr Gamma e1 t1 (@KEmpty e) ->
            M.add x t1 Gamma = Gamma' ->
            ty_expr Gamma' e2 t2 k ->
            ty_expr Gamma (ELet (EVar x) t1 e1 e2) t2 k 
| empty_ty : forall Gamma,
             ty_expr Gamma EEmpty TEmpty (@KEmpty e)
| seq_ty : forall Gamma e1 e2 t1 t2 k1 k2,
           ty_expr Gamma e1 t1 k1 ->
           ty_expr Gamma e2 t2 k2 ->
           ty_expr Gamma (ESeq e1 e2) (TSeq t1 t2) (KSeq e k1 k2).


