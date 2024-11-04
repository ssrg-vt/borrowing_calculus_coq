Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive expr : Type :=
| Var : ident -> expr
| Borrow : list ident -> expr -> expr
| Abs : list(ident * quantity * type) -> expr -> expr
| App : expr -> list expr -> expr
| Tuple : (expr * expr) -> expr
| Split : quantity -> list ident -> expr -> expr -> expr
| Cons : ident -> list expr -> expr
| Match : quantity -> expr -> list ((ident * list ident) * expr) -> expr.

(* Typing rules *)
Inductive type_expr : typing_context -> expr -> (quantity * type) -> typing_context -> Prop :=
| Ty_var_lin : forall Gamma x t,
              type_expr (extend_context Gamma x (Lin, t)) (Var x) (Lin, t) Gamma
| Ty_var_un : forall Gamma x t,
              type_expr (extend_context Gamma x (Un, t)) (Var x) (Un, t) (extend_context Gamma x (Un, t))
| Ty_var_bor : forall Gamma x t,
              type_expr (extend_context Gamma x (Bor, t)) (Var x) (Bor, t) (extend_context Gamma x (Bor, t)).
(* weakening: adding extra, unneeded assumptions to the typing context does not prevent the expr from type checking *)


           




