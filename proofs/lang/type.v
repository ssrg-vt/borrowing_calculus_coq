From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith kind.

Inductive primitive_ty : Type :=
| tint : primitive_ty
| tbool : primitive_ty
| tstring : primitive_ty.

Inductive ty_const : Type :=
| TyCon : primitive_ty ->  ty_const.

Inductive ty {e : Type} : Type :=
| TFun : ty -> kind e -> ty -> ty (* ty, effect, return ty *) 
| TCon : ty_const -> ty (* primitive, labels or new type *)
| TEmpty : ty
| TSeq : ty -> ty -> ty.


