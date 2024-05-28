From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg.
Require Export String ZArith.

(* Kinds *)

Inductive effect : Type :=
| div : effect
| total : effect
| exn : effect.

(* Kind constant *)
(* The kind constants for our purpose can be 
   exception (exn), 
   divergence (div) 
   non-determinstic (ndet) *)
Inductive kindCon : Type :=
| KindCon1 : effect -> kindCon
| KindCon2 : string -> kindCon.

(* Kind *)
Inductive kind : Type :=
| KEmpty : kind (* no effect *)
| KCon : kindCon -> kind (* effect type, effect row type *)
| KApp : kind -> kind -> kind (* function kind *).

(* Primitive kind constructors *)
Definition kindLabel := KCon (KindCon2 "X"). (* single effect: "exn", "div" *)
Definition kindStar := KCon (KindCon2 "V"). (* Value types *)


