From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type Coq.Structures.OrderedTypeEx.

Inductive expr : Type :=
| var_expr : string -> expr
| boolean_expr : bool -> expr
| cond_expr : expr -> expr -> expr -> expr
| abs_expr : string -> ty -> expr -> expr
| app_expr : expr -> expr -> expr.

Inductive ty_expr : typing_context -> expr -> ty -> Prop :=
| ty_var : forall x t Gamma1 Gamma2, 
           M.find x Gamma1 = Some t ->
           ty_expr (merge_context Gamma1 Gamma2) (var_expr x) t.
