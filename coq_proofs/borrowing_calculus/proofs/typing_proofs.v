Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers type expr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* add assumption about transposition related to equality of Gamma3 and Gamma3' *)
Lemma exchange : forall Gamma1 x1 t1 x2 t2 Gamma2 e t Gamma3 Gamma3',
type_expr (append_context (extend_context (extend_context Gamma1 x1 t1) x2 t2) Gamma2) e t Gamma3 ->
type_expr (append_context (extend_context (extend_context Gamma1 x2 t2) x1 t1) Gamma2) e t Gamma3'.
Proof.
Admitted.


(* weakening: adding extra, unneeded assumptions to the typing context does not prevent the expr from type checking *)
Lemma weakening: forall Gamma e T Gamma' x T',
type_expr Gamma e T Gamma' ->
type_expr (extend_context Gamma x T') e T (extend_context Gamma' x T').
Proof.
Admitted.
