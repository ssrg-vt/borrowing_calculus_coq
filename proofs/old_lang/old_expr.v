From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type.


(* Literals *)
Inductive lit : Type :=
| LitInt : Z -> lit
| LitString : string -> lit.

(* Expressions *)
Inductive expr {e : Type} : Type := 
| EVar : string -> expr
| ELit : lit -> expr
| ELam : expr -> @ty e -> expr -> expr (* Lambda x: t. e: f(x:t) = e *)
| EApp : expr -> expr -> expr (* e1 e2 *)
| ELet : expr -> @ty e -> expr -> expr -> expr (* let x : t = e1 in e2 *)
| EEmpty : expr 
| ESeq : expr -> expr -> expr (* e1; e2; ... *).


