From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.Structures.OrderedTypeEx type_context expr.

(* The predicate over Gamma is not affected by adding unrestricted variables *)
Lemma pred_context_q : forall q Gamma x t,
pred_context q Gamma ->
pred_context q (M.add x (qty un t) Gamma).
Proof.
move=> q Gamma x t [] q' x' Gamma' T h ht; subst.
apply predc with x (qty un t).
+ by apply P.F.add_eq_o; auto. 
apply predt with t un; auto.
apply q_refl.
Qed.

(* The predicate over Gamma is not affected by adding unrestricted variables *)
Lemma pred_context_un : forall Gamma x t,
subqual un (extract_qual t) ->
pred_context un Gamma ->
pred_context un (M.add x t Gamma).
Proof.
move=> Gamma x [] tq tp hs [] q' x' Gamma' T h [] T' q t' q'' heq hsub; subst. 
apply predc with x (qty tq tp). 
+ by apply P.F.add_eq_o; auto.
apply predt with tp tq; auto.
rewrite /extract_qual in hs. case: q hsub=> //= hsub.
case: tq hs=> //= hs.
+ by apply q_refl.
by apply q_linun.
Qed.

(* Exchange : If we can type check a term with context Gamma, then we can type check the 
              term with any permutation of the variables in Gamma *)
Lemma exchange : forall Gamma1 y yt x1 x2 t1 t2 e t,
ty_expr_nt (M.add y yt (M.add x2 t2 (M.add x1 t1 Gamma1))) e t ->
ty_expr_nt (M.add y yt (M.add x1 t1 (M.add x2 t2 Gamma1))) e t.
Proof. 
Admitted.

Lemma exchange2 : forall Gamma1 x1 x2 t1 t2 e t,
ty_expr_nt (M.add x2 t2 (M.add x1 t1 Gamma1)) e t ->
ty_expr_nt (M.add x1 t1 (M.add x2 t2 Gamma1)) e t.
Proof. 
Admitted.

(* Unrestricted weakening: Adding unrestricted variables to the context, does not prevent a term from type checking.*)
Lemma unrestricted_weakening : forall Gamma x e t t1,
ty_expr_nt Gamma e t ->
ty_expr_nt (M.add x (qty un t1) Gamma) e t.
Proof.
move=> Gamma x e t t1 h. induction h.
(* var *)
+ admit.
(* bool *)
+ constructor. by apply pred_context_q.
(* cond *)
+ apply ty_cond_nt with q (M.add x (qty un t1) Gamma1) (M.add x (qty un t1) Gamma2).
  + by apply IHh1.
  + by apply IHh2.
  + by apply IHh3.
  by apply m_un; auto.
(* pair *)
+ apply ty_pair_nt with (M.add x (qty un t1) Gamma1) (M.add x (qty un t1) Gamma2).
  + by apply IHh1.
  + by apply IHh2.
  + by apply H.
  + by apply H0.
  by apply m_un; auto.
(* split *)
+ apply ty_split_nt with (M.add x (qty un t1) Gamma1) (M.add x (qty un t1) Gamma2)
   q t0 t2 T1 T2.
 + apply IHh1.
 + have h := exchange2 (M.add x0 T1 Gamma2) y x T2 (qty un t1) e2 T IHh2. 
   by have := exchange Gamma2 y T2 x0 x T1 (qty un t1) e2 T h.
 by apply m_un; auto.
(* abs *)
+ apply ty_abs_nt with (Gamma := (M.add x (qty un t1) Gamma)).
  + by apply pred_context_q.
  + by have := exchange2 Gamma x0 x T1 (qty un t1) e T2 IHh.
(* app *)
apply ty_app_nt with (M.add x (qty un t1) Gamma1) (M.add x (qty un t1) Gamma2) T1 q. 
+ by apply IHh1.
+ by apply IHh2.
by apply m_un; auto.
Admitted.


