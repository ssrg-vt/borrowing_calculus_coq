From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith kind.

Inductive primitive_ty : Type :=
| tint : primitive_ty
| tbool : primitive_ty
| tstring : primitive_ty.

Inductive ty_var : Type :=
| TyVar : string -> kind -> ty_var.

Inductive ty_const : Type :=
| TyCon1 : primitive_ty -> kind -> ty_const
| TyCon2 : string -> kind -> ty_const.

Inductive ty : Type :=
| TFun : seq (string * ty) -> ty -> ty -> ty (* arg * ty, effect, return ty *)
| TCon : ty_const -> ty (* primitive, labels or new type *)
| TVar : ty_var -> ty (* type variables *).


Definition tconInt : ty_const := (TyCon1 tint kindStar).

Definition tconString : ty_const := (TyCon1 tstring kindStar).

Definition get_kind_ty_const (t : ty_const) : kind :=
match t with 
| TyCon1 p k => k
| TyCon2 s k => k
end.

Definition get_kind_ty_var (t : ty_var) : kind :=
match t with 
| TyVar s k => k
end.
