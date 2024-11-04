From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith.

(* Kinds *)

(* Effects can be divergence or exception as for now: we can extend this grammar later if needed *)
Inductive effect : Type :=
| div : effect
| exn : effect.

(* kindCon is made up of constant effects (like div or exn) or variable effects *)
Inductive kindCon (e : Type) : Type :=
| KindCon (e : effect) (* constant effect *)
| KindVar (k : e) (* variable effect depending on the polymorphic type *).


(* Kind : Represents the effect language *)
(* An empty effect, a single effect, a closed effect <e1, e2, e3, ...>, an open effect <e1, e2, e3, ...> | l *)
Inductive kind (e : Type) : Type :=
| KEmpty 
| KCon (k : kindCon effect) (* single effect type *)
| KSeq (k : kind e) (k' : kind e) (* row of effects : closed <e1, e2, e3> *) 
| KPoly (k : kind e) (k : kindCon e) (* open row of effects : <e1, e2, e3 | l> where l is polymorphic tail *).

(* Example :
   fun map (xs : list<a> , f : a -> e b) : e list<b> {
   match xs with 
    | Nil -> Nil
    | Cons (x, xx) -> Cons (f(x), xx.map(f)) *)

Section total_effect.

Variable (e : Type). 

Variable is_total : (kind e) -> bool.

Fixpoint are_total (k : seq (kind e)) : bool :=
match k with 
| [::] => true 
| k :: ks => is_total k && are_total ks
end. 

End total_effect.

(* never diverges or raises an exception *)
Fixpoint is_total {e : Type} (k : kind e) : bool :=
match k with 
| KEmpty => true 
| KCon k => match k with 
              | KindCon div => false 
              | KindCon exn => false
              | KindVar e => false  
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

Definition eq_kindCon (k1 k2 : kindCon effect) : bool := 
match k1, k2 with
| KindCon e1, KindCon e2 => eq_effect e1 e2
| KindVar l1, KindVar l2 => false (* need to fix *)
| _, _ => false
end.

Section eq_kinds.

Variable (e : Type). 

Variable eq_kind : kind e -> kind e -> bool.

Fixpoint eq_kinds (k1 k2 : seq (kind e)) : bool :=
match k1, k2 with 
| [::], [::] => true 
| k1 :: ks1, k2 :: ks2 => eq_kind k1 k2 && eq_kinds ks1 ks2
| _, _ => false
end.

End eq_kinds.

Fixpoint eq_kind {e : Type} (k1 k2 : kind e) : bool :=
match k1, k2 with 
| KEmpty, KEmpty => true 
| KCon k, KCon k' => eq_kindCon k k'
| KSeq k1 k1', KSeq k2 k2' => eq_kind k1 k2 && eq_kind k1' k2'
| KPoly k1 l1, KPoly k2 l2 => eq_kind k1 k2 (* need to fix for effect variable *)
| _, _ => false
end.

Fixpoint is_div_effect {e : Type} (k : kind e) : bool :=
match k with 
| KEmpty => false
| KCon k' => if (eq_kindCon (KindCon effect div) k') then true else false 
| KSeq k k' => if (eq_kind (KCon e (KindCon effect div)) k) then true else is_div_effect k'
| KPoly k l => is_div_effect k
end.

Fixpoint is_exn_effect {e : Type} (k : kind e) : bool :=
match k with 
| KEmpty => false
| KCon k' => if (eq_kindCon (KindCon effect exn) k') then true else false 
| KSeq k k' => if (eq_kind (KCon e (KindCon effect div)) k) then true else is_exn_effect k'
| KPoly k l => is_div_effect k
end.

Fixpoint is_div_mem {e : Type} (k : kind e) : bool :=
match k with 
| KEmpty => false
| KCon k => (eq_kindCon (KindCon effect div) k)
| KSeq k k' => is_div_mem k || is_div_mem k'
| KPoly k l => is_div_mem k 
end.

Fixpoint is_exn_mem {e : Type} (k : kind e) : bool :=
match k with 
| KEmpty => false
| KCon k => (eq_kindCon (KindCon effect exn) k)
| KSeq k k' => is_exn_mem k || is_exn_mem k'
| KPoly k l => is_exn_mem k 
end.

(* row of exn and div <exn, div> *)
Definition is_pure {e : Type} (k : kind e) : bool := is_div_mem k && is_exn_mem k.

(* Effect variable equivalence *) (* FIXME : No semantic meaning for variable effects *)
Inductive effect_var_equivalence {e : Type} : kindCon e -> kindCon e -> Prop :=
| EQ_var : forall e1 e2,
           effect_var_equivalence (KindVar e e1) (KindVar e e2).

(* Effect equivalence *)
Inductive kind_equivalence {e : Type} : kind e -> kind e -> Prop :=
| EQ_refl : forall k,
            kind_equivalence k k
| EQ_trans : forall k1 k2 k3,
             eq_kind k1 k2 = true ->
             kind_equivalence k1 k2 ->
             eq_kind k2 k3 = true ->
             kind_equivalence k2 k3 ->
             kind_equivalence k1 k3
| EQ_head : forall k1 e1 k2 e2,
            effect_var_equivalence e1 e2 -> (* bogus *)
            kind_equivalence k1 k2 ->
            kind_equivalence (KPoly e k1 (e1 : kindCon e)) (KPoly e k2 (e2 : kindCon e))
| EQ_swap : forall (k1 : kind e) (k2 : kind e) e1,
            (* ~(kind_equivalence k1 k2) ->*) (* How to define not equivalent relation *)
            kind_equivalence (KPoly e (KSeq e k1 k2) (e1 : kindCon e)) (KPoly e (KSeq e k2 k1) (e1 : kindCon e)).




