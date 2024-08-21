From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith type Coq.Structures.OrderedTypeEx type expr.

(* Exchange : If we can type check a term with context Gamma, then we can type check the 
              term with any permutation of the variables in Gamma *)
Lemma exchange : forall Gamma1 Gamma2 x1 x2 t1 t2 e t,
ty_expr (merge_context (M.add x2 t2 (M.add x1 t1 Gamma1)) Gamma2) e t ->
ty_expr (merge_context (M.add x1 t1 (M.add x2 t2 Gamma1)) Gamma2) e t.
Proof.
Admitted.
