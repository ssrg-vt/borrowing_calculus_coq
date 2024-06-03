From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type.


(* Literals *)
Inductive lit : Type :=
| LitInt : Z -> lit
| LitString : string -> lit.

(* Expressions *)
Inductive expr : Type := 
| EVar : string -> expr
| ELit : lit -> expr
| ELam : expr -> ty -> expr -> expr (* Lambda x: t. e f(x:t) = e *)
| EApp : expr -> expr -> expr (* e1 e2 *)
| ELet : expr -> ty -> expr -> expr -> expr (* let x : t = e1 in e2 *).


