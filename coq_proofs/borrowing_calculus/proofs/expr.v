Require Import String ZArith Coq.FSets.FMapAVL Coq.Structures.OrderedTypeEx.
Require Import Coq.FSets.FSetProperties Coq.FSets.FMapFacts FMaps FSetAVL Nat PeanoNat.
Require Import Coq.Arith.EqNat Coq.ZArith.Int Integers type.

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
               type_expr (extend_context Gamma x (Bor, t)) (Var x) (Bor, t) (extend_context Gamma x (Bor, t))
(* unrestricted variable can be used linearly or borrowed freely *)
| Ty_var_un_bor_lin : forall Gamma x q t,
                      List.In q (Lin :: Bor :: nil) ->
                      type_expr (extend_context Gamma x (Un, t)) (Var x) (q, t) (extend_context Gamma x (Un, t))
(* borrow should be only allowed in the region it is suppose to and after that it should be restored to its quantity *)
(* Question: about the variables to be borrowed *)
| Ty_borrow : forall Gamma xs ts e q t Gamma', 
              type_expr (append_only_bor Gamma xs ts) e (lift_quan q, t) (append_only_bor Gamma' xs ts) ->
              type_expr (append_only_lin Gamma xs ts) (Borrow xs e) (q, t) (append_only_lin Gamma' xs ts).
(*| Ty_abs_un : forall Gamma xs e,
              type_expr Gamma e 
              type_expr Gamma (Abs xs e).*)






           




