From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.Structures.OrderedTypeEx type_context_facts. 
Require Import typing_proofs_nt expr.

Lemma algorithmic_monotoicity : forall Gamma t T Gamma',
ty_expr Gamma t T Gamma' ->
unrestricted_part Gamma = unrestricted_part Gamma' /\
subset (linear_part Gamma') (linear_part Gamma).
Proof.
move=> Gamma t T Gamma' h. induction h.
(* un var *)
+ split=> //=. by apply subset_refl.
(* lin var *)
+ split=> //=. 
  + by apply unrestricted_lin.
  apply subset_append_linear_extend.
(* bool *)
+ split=> //=. by apply subset_refl.
(* cond *)
+ case: IHh1=> Ih1 Ih2. case: IHh2=> Ih3 Ih4. split=> //=.
  + by rewrite -Ih1 in Ih3.
  by move: (subset_trans (linear_part Gamma3) (linear_part Gamma2) (linear_part Gamma1) Ih4 Ih2).
(* pair *)
+ case: IHh1=> Ih1 Ih2. case: IHh2=> Ih1' Ih2'. split=> //=.
  + by rewrite -Ih1 in Ih1'.
  by move: (subset_trans (linear_part Gamma3) (linear_part Gamma2) (linear_part Gamma1) Ih2' Ih2).
(* split *)
+ case: IHh1=> Ih1 Ih2. case: IHh2=> Ih1' Ih2'. split=> //=.
  + rewrite Ih1. 
    have h := unrestricted_extend (extend_context Gamma2 x T1) Gamma3 y T2 Ih1'. 
    have h' := unrestricted_extend Gamma2 (remove_var_ty Gamma3 y T2) x T1 h. 
    by have -> := unrestricted_exchange Gamma3 x T1 y T2.
    have hs :=  subset_linear_extend Gamma3 y T2 (extend_context Gamma2 x T1) Ih2'. 
    have := subset_linear_extend (remove_var_ty Gamma3 y T2) x T1 Gamma2 hs.
    have -> := linear_exchange Gamma3 y T2 x T1. move=> hs'.
    by have := subset_trans (linear_part (remove_var_ty (remove_var_ty Gamma3 x T1) y T2))
            (linear_part Gamma2) (linear_part Gamma1) hs' Ih2.
(* abs *)
+ case: IHh=> IHh1 IHh2. split=> //=.
  + by apply unrestricted_extend.
  by apply subset_linear_extend.
(* app *)
case: IHh1=> IHh11 IHh12. case: IHh2=> IHh21 IHh22.
split=> //=.
+ by rewrite IHh11.
by have := subset_trans (linear_part Gamma3) (linear_part Gamma2) (linear_part Gamma1) 
        IHh22 IHh12.    
Qed.

Lemma algorithmic_weakening: forall Gamma e T Gamma' x T',
ty_expr Gamma e T Gamma' ->
ty_expr (extend_context Gamma x T') e T (extend_context Gamma' x T').
Proof.
move=> Gamma e T Gamma' x T' ht. induction ht.
(* unvar *)
+ admit.
(* linvar *)
+ admit.
(* bool *)
+ by apply ty_bool.
(* cond *)
+ apply ty_cond with q (extend_context Gamma2 x T').
  + by apply IHht1.
  + by apply IHht2.
  by apply IHht3.
(* pair *)
+ apply ty_pair with(extend_context Gamma2 x T').
  + by apply IHht1.
  + by apply IHht2.
  + by apply H.
  by apply H0.
(* split *)
+ have hs := ty_split (extend_context Gamma1 x T') 
                   (extend_context Gamma2 x T')
                   (extend_context Gamma3 x T') q e1 t1 t2 x0 y T1 T2 e2 T IHht1. 
  admit.
(* abs *)
+ have h := ty_abs x0 e q (extend_context Gamma1 x T') (extend_context Gamma2 x T') T1 T2.
  have hun : (q = un ->
       extend_context Gamma1 x T' = remove_var_ty (extend_context Gamma2 x T') x0 T1).
  + move=> hu. move: (H hu)=> he.
    case (string_dec x x0)=> //= hs.
    (* x = x0 *)
    + subst. admit. 
    admit.
  admit.
(* app *)
apply ty_app with (extend_context Gamma2 x T') T1 q.
+ by apply IHht1.
by apply IHht2.
Admitted.

Lemma is_mem_eq : forall x T l,
is_mem x ((x, T) :: l).
Proof.
simpl in |- *; auto.
move=> x T xs /=. 
case: ifP=> //= hx.
have hx' : (x =? x)%string. + by apply eqb_refl.
by rewrite hx' in hx.
Qed.

Lemma is_mem_hd : forall x T,
is_mem x [:: (x, T)].
Proof.
simpl in |- *; auto.
move=> x xs /=. 
case: ifP=> //= hx.
have hx' : (x =? x)%string. + by apply eqb_refl.
by rewrite hx' in hx.
Qed.

Lemma algorithmic_linear_strengthening : forall Gamma x T e T' Gamma',
ty_expr (extend_context Gamma x (qty lin T)) e T' (extend_context Gamma' x (qty lin T)) ->
ty_expr Gamma e T' Gamma'.
Proof.
move=> Gamma x T e T' Gamma' h. move: T T' Gamma' h. induction e=> //=.
Admitted.


