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

(* Map from string to type *)
(* Here ty (representing type is the value type) and string is the key *)
Definition typing_context := list (string * ty). 

(* Context Split *)
(* Describes how to split a single context into two context that will be used to type different subterms *)
Inductive context_split : typing_context -> typing_context -> typing_context -> Prop :=
| m_empty : context_split nil nil nil
| m_un : forall Gamma Gamma1 Gamma2 x t,
         context_split Gamma1 Gamma2 Gamma ->
         context_split (Gamma1 ++ [:: (x, (qty un t))]) (Gamma2 ++ [:: (x, (qty un t))]) 
         (Gamma ++ [:: (x, (qty un t))])
| m_lin1 : forall Gamma Gamma1 Gamma2 x t,
           context_split Gamma1 Gamma2 Gamma ->
           context_split (Gamma1 ++ [:: (x, (qty lin t))]) Gamma2 (Gamma ++ [:: (x, (qty lin t))])
| m_lin2 : forall Gamma Gamma1 Gamma2 x t,
           context_split Gamma1 Gamma2 Gamma ->
           context_split Gamma1 (Gamma2 ++ [:: (x, (qty lin t))]) (Gamma ++ [:: (x, (qty lin t))]).

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
          context_diff Gamma1 (Gamma2 ++ [:: (x, (qty lin t))]) Gamma3
| d_un : forall Gamma1 Gamma2 Gamma3 Gamma4 Gamma5 x t,
         context_diff Gamma1 Gamma2 Gamma3 ->
         Gamma3 = Gamma4 ++ [:: (x, qty un t)] ++ Gamma5 ->
         context_diff Gamma1 (Gamma2 ++ [:: (x, (qty lin t))]) (Gamma4 ++ Gamma5).

Definition eq_string_ty (s : string * ty) (s' : string * ty) : bool :=
if (String.eqb s.1 s'.1) && (eq_ty s.2 s'.2) then true else false.


Fixpoint remove_var_ty (t : typing_context) (k : string * ty): typing_context :=
match t with 
| nil => nil 
| x :: xs => if (eq_string_ty k x) then xs else x :: remove_var_ty xs k
end.
