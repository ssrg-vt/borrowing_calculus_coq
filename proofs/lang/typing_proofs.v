From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.Structures.OrderedTypeEx typing_proofs_nt expr.


Lemma merge_empty_context : forall Gamma,
merge_context Gamma empty_context = Gamma.
Proof.
Admitted.

(* Exchange : If we can type check a term with context Gamma, then we can type check the 
              term with any permutation of the variables in Gamma *)
(* How to ensure that Gamma3 is same as Gamma2 upto the transposition 
   of bindings of x1 and x2? *)
Lemma add_exchange2 : forall Gamma1 x1 x2 t1 t2 e t Gamma2,
x1 <> x2 ->
ty_expr (M.add x2 t2 (M.add x1 t1 Gamma1)) e t Gamma2 ->
exists Gamma3, ty_expr (M.add x1 t1 (M.add x2 t2 Gamma1)) e t Gamma3 /\ Gamma3 = Gamma2. 
Proof. 
Admitted.

Lemma add_exchange3 : forall Gamma1 y yt x1 x2 t1 t2 e t Gamma2,
x1 <> x2 ->
ty_expr (M.add y yt (M.add x2 t2 (M.add x1 t1 Gamma1))) e t Gamma2 ->
ty_expr (M.add y yt (M.add x1 t1 (M.add x2 t2 Gamma1))) e t Gamma2.
Proof.
Admitted.

Lemma remove_exchange2 : forall Gamma1 y x1 x2 t1 e t Gamma2,
ty_expr Gamma1 e t (M.remove y (M.remove x2 (M.add x1 t1 Gamma2))) ->
ty_expr Gamma1 e t (M.add x1 t1 (M.remove y (M.remove x2 Gamma2))).
Proof.
Admitted.

Lemma remove_add : forall y x (t: ty) Gamma,
y <> x ->
(M.remove y (M.add x t Gamma)) = (M.add x t (M.remove y Gamma)).
Proof.
Admitted.

Lemma merge_add : forall Gamma1 Gamma2 x1 T1 e T Gamma3 Gamma4,
ty_expr (merge_context (M.add x1 T1 Gamma1) Gamma2) e T Gamma3 ->
ty_expr (M.add x1 T1 (merge_context Gamma1 Gamma2)) e T Gamma4.
Proof. 
Admitted.

Lemma merge_add2 : forall Gamma1 Gamma2 x1 T1 x2 T2 e T Gamma3 Gamma4,
ty_expr (merge_context (M.add x2 T2 (M.add x1 T1 Gamma1)) Gamma2) e T Gamma3 ->
ty_expr (merge_context (M.add x1 T1 (M.add x2 T2 Gamma1)) Gamma2) e T Gamma4.
Proof.
Admitted.

Lemma deterministic_weakening : forall Gamma e T Gamma' x T',
ty_expr Gamma e T Gamma' ->
ty_expr (M.add x T' Gamma) e T (M.add x T' Gamma').
Proof.
move=> Gamma e T Gamma' x T' h. induction h.
(* uvar *)
+ have h := merge_add (M.add x0 (qty un T) Gamma1) Gamma2 x T' (var_expr x0) (qty un T)
            (merge_context (M.add x T' (M.add x0 (qty un T) Gamma1)) Gamma2)
            (M.add x T' (merge_context (M.add x0 (qty un T) Gamma1) Gamma2)).
  apply h. apply merge_add2 with (merge_context (M.add x0 (qty un T) (M.add x T' Gamma1)) Gamma2). by apply ty_uvar.
(* lvar *)
+ have h := merge_add (M.add x0 (qty lin T) Gamma1) Gamma2 x T' (var_expr x0) (qty lin T)
          (merge_context Gamma1 Gamma2) (M.add x T' (merge_context Gamma1 Gamma2)).
  apply h. apply merge_add2 with (merge_context (M.add x T' Gamma1) Gamma2). by apply ty_lvar.
(* bool *)
+ by apply ty_bool.
(* cond *)
+ apply ty_cond with q (M.add x T' Gamma2).
  + by apply IHh1.
  + by apply IHh2.
  by apply IHh3.
(* pair *)
+ apply ty_pair with (M.add x T' Gamma2).
  + by apply IHh1.
  + by apply IHh2.
  + by apply H.
  by apply H0.
(* split *)
+ admit.
(* abs *)
+ admit.
(* app *)
apply ty_app with (M.add x T' Gamma2) T1 q.
+ by apply IHh1.
by apply IHh2.
Admitted.

(* If there is a linear variable that is not being used in the evaluation of e then 
   e typechecks in the context that does not include any information about
   the linear variable *)
Lemma deterministic_linear_strengthening : forall Gamma x T e T' Gamma',
ty_expr (M.add x (qty lin T) Gamma) e T' (M.add x (qty lin T) Gamma') ->
ty_expr Gamma e T' Gamma'. 
Proof.
Admitted.


