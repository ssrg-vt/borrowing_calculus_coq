From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith.

(* Kinds *)

Inductive effect : Type :=
| div : effect
| exn : effect.

(* Kind constant *)
(* The kind constants for our purpose can be 
   exception (exn), 
   divergence (div) 
   non-determinstic (ndet) *)
Inductive kindCon : Type :=
| KindCon1 : effect -> kindCon (* single effect *)
| KindCon2 : string -> kindCon (* effect labels *).

(* Kind *)
Inductive kind : Type :=
| KEmpty : kind (* no effect *)
| KCon : kindCon -> kind (* single effect type *)
| KSeq : kind -> kind -> kind (* row of effects : closed <e1, e2, e3> *) 
| KPoly : kind -> kindCon -> kind (* open row of effects : <e1, e2, e3 | l> where l is polymorphic tail *).

(* Example :
   fun map (xs : list<a> , f : a -> e b) : e list<b> {
   match xs with 
    | Nil -> Nil
    | Cons (x, xx) -> Cons (f(x), xx.map(f)) *)

Section total_effect.

Variable is_total : kind -> bool.

Fixpoint are_total (k : seq kind) : bool :=
match k with 
| [::] => true 
| k :: ks => is_total k && are_total ks
end. 

End total_effect.

(* never diverges or raises an exception *)
Fixpoint is_total (k : kind) : bool :=
match k with 
| KEmpty => true 
| KCon k => match k with 
              | KindCon1 div => false 
              | KindCon1 exn => false
              | KindCon2 e => false  
            end
| KSeq k k' => is_total k && is_total k'
| KPoly k l => false
end.

Definition eq_effect (k1 k2 : effect) : bool :=
match k1, k2 with 
| div, div => true 
| exn, exn => true 
| _, _ => false
end.

Definition eq_kindCon (k1 k2 : kindCon) : bool := 
match k1, k2 with
| KindCon1 e1, KindCon1 e2 => eq_effect e1 e2
| KindCon2 l1, KindCon2 l2 => eqb l1 l2
| _, _ => false
end.

Section eq_kinds.

Variable eq_kind : kind -> kind -> bool.

Fixpoint eq_kinds (k1 k2 : seq kind) : bool :=
match k1, k2 with 
| [::], [::] => true 
| k1 :: ks1, k2 :: ks2 => eq_kind k1 k2 && eq_kinds ks1 ks2
| _, _ => false
end.

End eq_kinds.

Fixpoint eq_kind (k1 k2 : kind) : bool :=
match k1, k2 with 
| KEmpty, KEmpty => true 
| KCon k, KCon k' => eq_kindCon k k'
| KSeq k1 k1', KSeq k2 k2' => eq_kind k1 k2 && eq_kind k1' k2'
| KPoly k1 l1, KPoly k2 l2 => eq_kind k1 k2 && eq_kindCon l1 l2
| _, _ => false
end.

Fixpoint is_div_effect (k : kind) : bool :=
match k with 
| KEmpty => false
| KCon k' => if (eq_kindCon (KindCon1 div) k') then true else false 
| KSeq k k' => if (eq_kind (KCon (KindCon1 div)) k) then true else is_div_effect k'
| KPoly k l => is_div_effect k
end.

Fixpoint is_exn_effect (k : kind) : bool :=
match k with 
| KEmpty => false
| KCon k' => if (eq_kindCon (KindCon1 exn) k') then true else false 
| KSeq k k' => if (eq_kind (KCon (KindCon1 div)) k) then true else is_exn_effect k'
| KPoly k l => is_div_effect k
end.

Fixpoint is_div_mem (k : kind) : bool :=
match k with 
| KEmpty => false
| KCon k => (eq_kindCon (KindCon1 div) k)
| KSeq k k' => is_div_mem k || is_div_mem k'
| KPoly k l => is_div_mem k 
end.

Fixpoint is_exn_mem (k : kind) : bool :=
match k with 
| KEmpty => false
| KCon k => (eq_kindCon (KindCon1 exn) k)
| KSeq k k' => is_exn_mem k || is_exn_mem k'
| KPoly k l => is_exn_mem k 
end.

(* row of exn and div <exn, div> *)
Definition is_pure (k : kind) : bool := is_div_mem k && is_exn_mem k.

(* Effect equivalence *)
Inductive effect_equivalence : kind -> kind -> Prop :=
| EQ_refl : forall k,
            effect_equivalence k k
| EQ_trans : forall k1 k2 k3,
             eq_kind k1 k2 = true ->
             effect_equivalence k1 k2 ->
             eq_kind k2 k3 = true ->
             effect_equivalence k2 k3 ->
             effect_equivalence k1 k3.


