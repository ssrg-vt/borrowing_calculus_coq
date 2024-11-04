Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ident := positive.

Inductive quantity : Type :=
| Bor : quantity
| Lin : quantity
| Un : quantity.

Inductive type: Type :=
| Prod : (type * type) -> type 
| Seq : list type -> type
| Sum : list (ident * type) -> type
| Arrow : list (quantity * type) -> type -> type.


Definition eq_quantity (q1 q2 : quantity) : bool :=
match q1, q2 with 
| Bor, Bor => true 
| Lin, Lin => true 
| Un, Un => true 
| _, _ => false
end. 

Fixpoint unzip1 {A} {B} (es : list (A * B)) : list A :=
match es with 
| nil => nil
| e :: es => fst(e) :: unzip1 es
end.

Fixpoint unzip2 {A} {B} (es : list (A * B)) : list B :=
match es with 
| nil => nil
| e :: es => snd(e) :: unzip2 es
end.

Fixpoint zip {A} {B} (es1 : list A) (es2 : list B) : list (A * B) :=
match es1, es2 with 
| nil, nil => nil
| e1 :: es1, e2 :: es2 => (e1, e2) :: zip es1 es2
| _, _ => nil
end.

Fixpoint eq_idents (ids1 ids2 : list ident) : bool :=
match ids1, ids2 with 
| nil, nil => true 
| id1 :: ids1, id2 :: ids2 => (id1 =? id2)%positive && eq_idents ids1 ids2
| _, _ => false
end.

Fixpoint eq_quantities (qs1 qs2 : list quantity) : bool :=
match qs1, qs2 with 
| nil, nil => true 
| q1 :: qs1, q2 :: qs2 => eq_quantity q1 q2 && eq_quantities qs1 qs2 
| _ , _ => false
end. 

Section Eq_types.

Variable eq_type : type -> type -> bool.

Fixpoint eq_types (ts1 ts2 : list type) : bool :=
match ts1, ts2 with 
| nil, nil => true 
| t1 :: ts1, t2 :: ts2 => eq_type t1 t2 && eq_types ts1 ts2 
| _, _ => false
end.

Fixpoint eq_quans_types (ts1 ts2 : list (quantity * type)) : bool :=
match ts1, ts2 with 
| nil, nil => true
| t1 :: ts1, t2 :: ts2 => eq_quantity (fst t1) (fst t2) && eq_type (snd t1) (snd t2) && eq_quans_types ts1 ts2
| _, _ => false
end.

Fixpoint eq_idents_types (ts1 ts2 : list (ident * type)) : bool :=
match ts1, ts2 with 
| nil, nil => true
| t1 :: ts1, t2 :: ts2 => ((fst t1) =? (fst t2))%positive && eq_type (snd t1) (snd t2) && eq_idents_types ts1 ts2
| _, _ => false
end.

End Eq_types. 

Fixpoint eq_type (t1 t2 : type) : bool :=
match t1, t2 with 
| Prod(t1, t2), Prod(t1', t2') => eq_type t1 t1' && eq_type t2 t2'
| Seq ts1, Seq ts2 => eq_types eq_type ts1 ts2
| Sum ts1, Sum ts2 => eq_idents_types eq_type ts1 ts2
| Arrow ts1 t1, Arrow ts2 t2 => eq_quans_types eq_type ts1 ts2 && eq_type t1 t2
| _, _ => false
end. 


Definition eq_quan_type (t1 t2 : (quantity * type)) : bool :=
eq_quantity (fst t1) (fst t2) && eq_type (snd t1) (snd t2).


(* Typing context *)
Definition typing_context := list (ident * (quantity * type)). 

Fixpoint remove_var_quan_ty (t : typing_context) (k : ident) (ty : quantity * type) : typing_context :=
match t with 
| nil => nil 
| x :: xs => if (k =? (fst x))%positive && eq_quan_type (snd x) ty then xs else x :: remove_var_quan_ty xs k ty
end.

Fixpoint is_mem (k : ident) (t : typing_context) : bool :=
match t with 
| nil => false
| x :: xs => if (k =? (fst x))%positive then true else is_mem k xs
end.

Fixpoint extend_context (t : typing_context) (k : ident) (v : quantity * type) : typing_context := 
match t with 
| nil => (k, v) :: nil 
| h :: t => if (k =? (fst h))%positive then (k, v) :: t else h :: extend_context t k v
end. 

Fixpoint append_context (t1 : typing_context) (t2 : typing_context) : typing_context :=
match t2 with 
| nil => t1
| h :: t =>  append_context (extend_context t1 (fst h) (snd h)) t
end.


Fixpoint append_only_lin (Gamma : typing_context) (xs : list ident) (ts : list type) : typing_context :=
match xs with 
| nil => nil
| x :: xs => match ts with 
             | nil => nil
             | t :: ts => append_only_lin (extend_context Gamma x (Lin, t)) xs ts
             end 
end. 

Fixpoint append_only_bor (Gamma : typing_context) (xs : list ident) (ts : list type) : typing_context :=
match xs with 
| nil => nil
| x :: xs => match ts with 
             | nil => nil
             | t :: ts => append_only_bor (extend_context Gamma x (Bor, t)) xs ts
             end 
end. 

Definition lift_quan (q : quantity) : quantity :=
match q with
| Bor => Un
| Lin => Lin 
| Un => Un
end.

Fixpoint filer_context (acc : typing_context) (Gamma : typing_context) (q : quantity) : typing_context :=
match Gamma with 
| nil => nil
| x :: xs => if (eq_quantity (fst(snd x)) q) then append_context acc (x :: nil) else filer_context acc xs q
end. 
