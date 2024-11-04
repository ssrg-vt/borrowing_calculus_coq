From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat Coq.Arith.EqNat. 

(***** Type System ******)

(* Type qualifiers *)
(* lin : linear qualifier indicates that the data structure in question will be used exactly once in the program 
         (operationally we deallocate these linear values immediately after they are used)
   un : unrestricted qualifier indicates that data can be used many times as desired 
        (the memory resources will be automatically recycled by some  mechanism like garbage collector) *) 
Inductive qual : Type := 
| lin : qual 
| un : qual.

Inductive subqual : qual -> qual -> Prop :=
| q_refl : forall q q', subqual q q'
| q_linun : subqual lin un 
| q_trans : forall q q' q'',
            subqual q q' ->
            subqual q' q'' ->
            subqual q q''.

(* Types *)
Inductive pty : Type := 
| bool_ty : pty
| pair_ty : ty -> ty -> pty
| arrow_ty : ty -> ty -> pty

with ty : Type :=
| qty : qual -> pty -> ty.

Definition extract_qual (t : ty) := 
match t with
| qty q t => q
end.

Definition eq_qual (q1 q2 : qual) : bool :=
match q1, q2 with 
| lin, lin => true 
| un, un => true 
| _, _ => false
end.

Fixpoint eq_pty (p1 p2 : pty) : bool := 
match p1, p2 with 
| bool_ty, bool_ty => true 
| pair_ty t1 t2, pair_ty t3 t4 => eq_ty t1 t3 && eq_ty t2 t4 
| arrow_ty t1 t2, arrow_ty t3 t4 => eq_ty t1 t3 && eq_ty t2 t4
| _, _ => false
end
with eq_ty (t1 t2 : ty) : bool :=
match t1, t2 with 
| qty q1 t1, qty q2 t2 => if eq_qual q1 q2 then eq_pty t1 t2 else false 
end.

Scheme pty_Ind := Induction for pty Sort Prop
 with ty_Ind := Induction for ty Sort Prop.

Combined Scheme pty_ty_Ind from pty_Ind, ty_Ind. 

(*Section pty_pred.
Variable Ppty : pty -> Prop.
Variable Pty : ty -> Prop.
Variable Bpty : Ppty bool_ty.
Variable 
Fixpoint pty_Ind (p : pty) : (Ppty p) :=
match p with 
| bool_ty => Bpty
| pair_ty t1 t2 => (Pty t1) /\ (Pty t2)
| arrow_ty t1 t2 => (Pty t1) /\ (Pty t2)
end.
End pty_pred.*)

(* Map from string to type *)
(* Here ty (representing type is the value type) and string is the key *)
Definition typing_context := list (string * ty). 

Definition eq_string_ty (s : string * ty) (s' : string * ty) : bool :=
if (String.eqb s.1 s'.1) && (eq_ty s.2 s'.2) then true else false.


Fixpoint remove_var_ty (t : typing_context) (k : string) (T : ty) : typing_context :=
match t with 
| nil => nil 
| x :: xs => if (String.eqb k x.1 && eq_ty T x.2) then xs else x :: remove_var_ty xs k T
end.

Fixpoint is_mem (k : string) (t : typing_context) : bool :=
match t with 
| nil => false
| x :: xs => if (String.eqb k x.1) then true else is_mem k xs
end.

Fixpoint extend_context (t : typing_context) (k : string) (v : ty) : typing_context := 
match t with 
| nil => [:: (k, v)]
| h :: t => if (String.eqb k h.1) then (k, v) :: t else h :: extend_context t k v
end. 

Fixpoint append_context (t1 : typing_context) (t2 : typing_context) : typing_context :=
match t2 with 
| nil => t1
| h :: t =>  append_context (extend_context t1 h.1 h.2) t
end.

Fixpoint subset (t1 : typing_context) (t2 : typing_context) : bool :=
match t1 with 
| nil => true 
| h :: t => if is_mem h.1 t2 then subset t t2 else false
end.

Definition check_unrestricted_ty (t : ty) : bool :=
match t with 
| qty un p => true 
| qty lin p => false
end.

Definition check_linear_ty (t : ty) : bool :=
match t with 
| qty un p => false 
| qty lin p => true
end.
 
Fixpoint unrestricted_part (Gamma : typing_context) : typing_context :=
match Gamma with 
| nil => nil
| t :: ts => if (check_unrestricted_ty t.2) then t :: unrestricted_part ts else unrestricted_part ts
end.

Fixpoint linear_part (Gamma : typing_context) : typing_context :=
match Gamma with 
| nil => nil
| t :: ts => if (check_linear_ty t.2) then t :: linear_part ts else linear_part ts
end.

Lemma unrestricted_cat : forall Gamma1 Gamma2, 
unrestricted_part (Gamma1 ++ Gamma2) = unrestricted_part Gamma1 ++ unrestricted_part Gamma2.
Proof.
induction Gamma1 as [ | h t IH]; simpl; auto. move=> Gamma2.
case: ifP=> //= hc. by rewrite IH.
Qed.

Lemma linear_cat : forall Gamma1 Gamma2, 
linear_part (Gamma1 ++ Gamma2) = linear_part Gamma1 ++ linear_part Gamma2.
Proof.
induction Gamma1 as [ | h t IH]; simpl; auto. move=> Gamma2.
case: ifP=> //= hc. by rewrite IH.
Qed.

Lemma unrestricted_tail : forall x T Gamma,
unrestricted_part ((x, qty lin T) :: Gamma) = unrestricted_part Gamma.
Proof.
by induction Gamma as [ | h t IH]; simpl; auto.
Qed.

Lemma linear_tail : forall x T Gamma,
linear_part ((x, qty un T) :: Gamma) = linear_part Gamma.
Proof.
by induction Gamma as [ | h t IH]; simpl; auto.
Qed.

Lemma subset_tail : forall h t1 t2,
subset t1 t2 ->
subset (h :: t1) (h :: t2).
Proof.
Admitted.

Lemma subset_refl : forall Gamma,
subset Gamma Gamma = true.
Proof.
intros. induction Gamma as [ | h t IH]; auto.
Admitted.

(* Context Split *)
(* Describes how to split a single context into two context that will be used to type different subterms *)
Inductive context_split : typing_context -> typing_context -> typing_context -> Prop :=
| m_empty : context_split nil nil nil
| m_un : forall Gamma Gamma1 Gamma2 x t,
         context_split Gamma1 Gamma2 Gamma ->
         context_split (extend_context Gamma1 x (qty un t)) (extend_context Gamma2 x (qty un t))
         (extend_context Gamma x (qty un t))
| m_lin1 : forall Gamma Gamma1 Gamma2 x t,
           context_split Gamma1 Gamma2 Gamma ->
           context_split (extend_context Gamma1 x (qty lin t)) Gamma2 (extend_context Gamma x (qty lin t))
| m_lin2 : forall Gamma Gamma1 Gamma2 x t,
           context_split Gamma1 Gamma2 Gamma ->
           context_split Gamma1 (extend_context Gamma2 x (qty lin t)) (extend_context Gamma x (qty lin t)).

(* Predicate over types *)
(* Unrestricted data strutures may not contain linear data structures *)
(* un <x, y> should not contain any variable of qualifier lin *)
(* Linear data structures can hold objects with linear or unrestricted type, 
   but unrestricted data structures can only hold objects with unrestricted type. *)
Inductive pred_ty : qual -> ty -> Prop :=
| predt : forall T q t q',
          T = (qty q' t) ->
          subqual q q' ->
          pred_ty q T.

Inductive pred_context : qual -> typing_context -> Prop :=
| predc : forall q x Gamma T,
          List.In (x, T) Gamma ->
          pred_ty q T ->
          pred_context q Gamma. 


(***** Deterministic Type System ******)

(* Context Diff *) 
(* Describes how to compute the rest of the context for the next subterm *)
Inductive context_diff : typing_context -> typing_context -> typing_context -> Prop :=
| d_empty : forall Gamma, context_diff Gamma nil Gamma
| d_lin : forall Gamma1 Gamma2 Gamma3 x t,
          context_diff Gamma1 Gamma2 Gamma3 ->
          List.In (x, qty lin t) Gamma3 = false  ->
          context_diff Gamma1 (extend_context Gamma2 x (qty lin t)) Gamma3
| d_un : forall Gamma1 Gamma2 Gamma3 Gamma4 Gamma5 x t,
         context_diff Gamma1 Gamma2 Gamma3 ->
         Gamma3 = append_context (extend_context Gamma4 x (qty un t)) Gamma5 ->
         context_diff Gamma1 (extend_context Gamma2 x (qty lin t)) (append_context Gamma4 Gamma5).
