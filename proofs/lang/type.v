From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL.

(***** Type System ******)

(* Types *)
Inductive ty : Type := 
| bool_ty : ty
| arrow_ty : ty -> ty -> ty.

(* Typing enviornment: Maps variable names to their type *)
Module M := FMapAVL.Make String_as_OT.
Module P := WProperties_fun String_as_OT M.
Module F := P.F.

(* Map from string to type: Map is build using a AVL tree for fast operations *)
(* Here ty (representing type is the value type) and string is the key *)
Definition typing_context := M.t ty. 

Fixpoint add_keys_vals (ks : list (M.Raw.key*ty)) (c1 : M.Raw.tree ty) : M.Raw.tree ty :=
match ks with 
| [::] => c1
| k :: ks => add_keys_vals ks (M.Raw.add k.1 k.2 c1)
end.

Definition add_raw_context (c1 : M.Raw.tree ty) (c2 : M.Raw.tree ty) : M.Raw.tree ty :=
let ks := M.Raw.elements_aux [::] c1 in
add_keys_vals ks c2.

Lemma merge_context_prop : forall t1 t2,
M.Raw.bst (add_raw_context (M.this t1) (M.this t2)).
Proof.
Admitted.

Definition merge_context (t1 : typing_context) (t2 : typing_context) : typing_context
:= {| M.this := add_raw_context (M.this t1) (M.this t2); 
      M.is_bst := merge_context_prop t1 t2 |}. 
