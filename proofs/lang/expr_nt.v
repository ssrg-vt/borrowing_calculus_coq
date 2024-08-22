From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type_nt Coq.Structures.OrderedTypeEx.

(**** Expression ****)
Inductive expr : Type :=
| var_expr : string -> expr                         (* x *)
| bool_expr : qual -> bool -> expr                  (* q b *)
| cond_expr : expr -> expr -> expr -> expr          (* if e then e1 else e2 *)
| pair_expr : qual -> expr -> expr -> expr          (* q<e1, e2> *)
| split_expr : expr -> expr -> expr -> expr -> expr (* split e1 as x, y in e2 *)
| abs_expr : qual -> string -> ty -> expr -> expr   (* q f(x:t) = e *)
| app_expr : expr -> expr -> expr.                  (* e1 e2 *)


(**** Typing rules ****)
Inductive ty_expr : typing_context -> expr -> ty -> Prop :=
(* No linear variable is discarded without being used *)
| ty_var : forall x T Gamma1 Gamma2, 
           pred_context un (merge_context Gamma1 Gamma2) ->
           ty_expr (merge_context (M.add x T Gamma1) Gamma2) (var_expr x) T
| ty_bool : forall q b Gamma,
            pred_context un Gamma ->
            ty_expr Gamma (bool_expr q b) (qty q bool_ty)
(* typing context Gamma3 is split into Gamma1 and Gamma2
   Gamma1 is used to type check the conditional expression. 
   Gamma2 is used to type check the then and else branch.
   Ensures that a particular linear variable appears once in e2 and once in e3 (rules m_lin1 and m_lin2).
   The particular linear object bound to variable will be executed once at runtime as 
   either true or false branch will be executed. *)
| ty_cond : forall e1 q e2 e3 Gamma1 Gamma2 Gamma3 T,
            ty_expr Gamma1 e1 (qty q bool_ty) ->
            ty_expr Gamma2 e2 T ->
            ty_expr Gamma2 e3 T ->
            context_split Gamma1 Gamma2 Gamma3 ->
            ty_expr Gamma3 (cond_expr e1 e2 e3) T
| ty_pair : forall Gamma1 Gamma2 Gamma3 e1 e2 T1 T2 q,
            ty_expr Gamma1 e1 T1 ->
            ty_expr Gamma2 e2 T2 ->
            pred_ty q T1 ->
            pred_ty q T2 ->
            context_split Gamma1 Gamma2 Gamma2 ->
            ty_expr Gamma3 (pair_expr q e1 e2) (qty q (pair_ty T1 T2))
| ty_split : forall Gamma1 Gamma2 Gamma3 q e1 t1 t2 x y T1 T2 e2 T,
             ty_expr Gamma1 e1 (qty q (pair_ty t1 t2)) ->
             ty_expr (M.add y T2 (M.add x T1 Gamma2)) e2 T ->
             context_split Gamma1 Gamma2 Gamma3 ->
             ty_expr Gamma3 (split_expr e1 (var_expr x) (var_expr y) e2) T 
| ty_abs : forall x e q Gamma T1 T2,
           pred_context q Gamma -> 
           ty_expr (M.add x T1 Gamma) e T2 ->
           ty_expr Gamma (abs_expr q x T1 e) (qty q (arrow_ty T1 T2))
| ty_app : forall e1 e2 Gamma1 Gamma2 Gamma3 T1 T2 q,
           ty_expr Gamma1 e1 (qty q (arrow_ty T1 T2)) ->
           ty_expr Gamma2 e2 T1 ->
           context_split Gamma1 Gamma2 Gamma3 ->
           ty_expr Gamma3 (app_expr e1 e2) T2.
           

