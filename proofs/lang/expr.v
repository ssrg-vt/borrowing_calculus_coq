From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type Coq.Structures.OrderedTypeEx.

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
(* The relation also returns left-over context along with the type *)
Inductive ty_expr : typing_context -> expr -> ty -> typing_context -> Prop :=
| ty_uvar : forall x T Gamma1 Gamma2, 
           ty_expr (merge_context (M.add x (qty un T) Gamma1) Gamma2) (var_expr x) (qty un T) 
           (merge_context (M.add x (qty un T) Gamma1) Gamma2)
| ty_lvar : forall x T Gamma1 Gamma2, 
           ty_expr (merge_context (M.add x (qty lin T) Gamma1) Gamma2) (var_expr x) (qty lin T) 
           (merge_context Gamma1 Gamma2)
| ty_bool : forall q b Gamma,
            ty_expr Gamma (bool_expr q b) (qty q bool_ty) Gamma
| ty_cond : forall e1 q e2 e3 Gamma1 Gamma2 Gamma3 T,
            ty_expr Gamma1 e1 (qty q bool_ty) Gamma2 ->
            ty_expr Gamma2 e2 T Gamma3 ->
            ty_expr Gamma2 e3 T Gamma3 ->
            ty_expr Gamma1 (cond_expr e1 e2 e3) T Gamma3
| ty_pair : forall Gamma1 Gamma2 Gamma3 e1 e2 T1 T2 q,
            ty_expr Gamma1 e1 T1 Gamma2 ->
            ty_expr Gamma2 e2 T2 Gamma3 ->
            pred_ty q T1 ->
            pred_ty q T2 ->
            ty_expr Gamma1 (pair_expr q e1 e2) (qty q (pair_ty T1 T2)) Gamma3
| ty_split : forall Gamma1 Gamma2 Gamma3 q e1 t1 t2 x y T1 T2 e2 T,
             ty_expr Gamma1 e1 (qty q (pair_ty t1 t2)) Gamma2 ->
             ty_expr (M.add y T2 (M.add x T1 Gamma2)) e2 T Gamma3 ->
             ty_expr Gamma1 (split_expr e1 (var_expr x) (var_expr y) e2) T 
             (M.remove y (M.remove x Gamma3))
| ty_abs : forall x e q Gamma1 Gamma2 T1 T2,
           (q = un -> Gamma1 = M.remove x Gamma2) ->
           ty_expr (M.add x T1 Gamma1) e T2 Gamma2 ->
           ty_expr Gamma1 (abs_expr q x T1 e) (qty q (arrow_ty T1 T2)) (M.remove x Gamma2)
| ty_app : forall e1 e2 Gamma1 Gamma2 Gamma3 T1 T2 q,
           ty_expr Gamma1 e1 (qty q (arrow_ty T1 T2)) Gamma2 ->
           ty_expr Gamma2 e2 T1 Gamma3 ->
           ty_expr Gamma1 (app_expr e1 e2) T2 Gamma3.
