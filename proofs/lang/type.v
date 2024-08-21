From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL.

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
| q_relf : forall q q', subqual q q'
| q_linun : subqual lin un 
| q_trans : forall q q' q'',
            subqual q q' ->
            subqual q' q'' ->
            subqual q q''.

(* Types *)
Inductive ty : Type := 
| bool_ty : ty
| pair_ty : ty -> ty -> ty
| arrow_ty : ty -> ty -> ty.

(* Typing enviornment: Maps variable names to their type *)
Module M := FMapAVL.Make String_as_OT.
Module P := WProperties_fun String_as_OT M.
Module F := P.F.

(* Map from string to type: Map is build using a AVL tree for fast operations *)
(* Here ty (representing type is the value type) and string is the key *)
Definition typing_context := M.t (qual * ty). 

Definition empty_typing_context := (M.empty (qual * ty)).

Fixpoint add_keys_vals (ks : list (M.Raw.key*(qual * ty))) (c1 : M.Raw.tree (qual * ty)) 
: M.Raw.tree (qual * ty) :=
match ks with 
| [::] => c1
| k :: ks => add_keys_vals ks (M.Raw.add k.1 k.2 c1)
end.

Definition add_raw_context (c1 : M.Raw.tree (qual * ty)) (c2 : M.Raw.tree (qual * ty)) : M.Raw.tree (qual * ty) :=
let ks := M.Raw.elements_aux [::] c1 in
add_keys_vals ks c2.

Lemma merge_context_prop : forall t1 t2,
M.Raw.bst (add_raw_context (M.this t1) (M.this t2)).
Proof.
Admitted.

Definition merge_context (t1 : typing_context) (t2 : typing_context) : typing_context
:= {| M.this := add_raw_context (M.this t1) (M.this t2); 
      M.is_bst := merge_context_prop t1 t2 |}. 

(* Context Split *)
(* Describes how to split a single context into two context that will be used to type different subterms *)
Inductive context_split : typing_context -> typing_context -> typing_context -> Prop :=
| m_empty : context_split empty_typing_context empty_typing_context empty_typing_context
| m_un : forall Gamma Gamma1 Gamma2 x t,
         context_split Gamma1 Gamma2 Gamma ->
         context_split (M.add x (un, t) Gamma1) (M.add x (un,t) Gamma2) (M.add x (un,t) Gamma)
| m_lin1 : forall Gamma Gamma1 Gamma2 x t,
           context_split Gamma1 Gamma2 Gamma ->
           context_split (M.add x (lin, t) Gamma1) Gamma2 (M.add x (lin, t) Gamma)
| m_lin2 : forall Gamma Gamma1 Gamma2 x t,
           context_split Gamma1 Gamma2 Gamma ->
           context_split Gamma1 (M.add x (lin, t) Gamma2) (M.add x (lin, t) Gamma).

(* Predicate over types *)
(* Unrestricted data strutures may not contain linear data structures *)
(* un <x, y> should not contain any variable of qualifier lin *)
(* Linear data structures can hold objects with linear or unrestricted type, 
   but unrestricted data structures can only hold objects with unrestricted type. *)
Inductive pred_ty : qual -> (qual * ty) -> Prop :=
| predt : forall T q t q',
          T = (q', t) ->
          subqual q q' ->
          pred_ty q T.

Inductive pred_context : qual -> typing_context -> Prop :=
| predc : forall q x Gamma T,
          M.find x Gamma = Some T ->
          pred_ty q T ->
          pred_context q Gamma. 
