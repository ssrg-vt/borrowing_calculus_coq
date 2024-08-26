From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Export String ZArith type_context Coq.Structures.OrderedTypeEx.

(**** Expression ****)
Inductive expr : Type :=
| var_expr : string -> expr                         (* x *)
| bool_expr : qual -> bool -> expr                  (* q b *)
| cond_expr : expr -> expr -> expr -> expr          (* if e then e1 else e2 *)
| pair_expr : qual -> expr -> expr -> expr          (* q<e1, e2> *)
| split_expr : expr -> expr -> expr -> expr -> expr (* split e1 as x, y in e2 *)
| abs_expr : qual -> string -> ty -> expr -> expr   (* q f(x:t) = e *)
| app_expr : expr -> expr -> expr.                  (* e1 e2 *)


(**** Non-deterministic Typing rules ****) Check List.partition.
Inductive ty_expr_nt : typing_context -> expr -> ty -> Prop :=
(* No linear variable is discarded without being used *)
| ty_var_nt : forall x T Gamma1 Gamma2, 
              pred_context un (Gamma1 ++ Gamma2) ->
              ty_expr_nt (Gamma1 ++ [::(x, T)] ++ Gamma2) (var_expr x) T
| ty_bool_nt : forall q b Gamma,
               pred_context un Gamma ->
               ty_expr_nt Gamma (bool_expr q b) (qty q bool_ty)
(* typing context Gamma3 is split into Gamma1 and Gamma2
   Gamma1 is used to type check the conditional expression. 
   Gamma2 is used to type check the then and else branch.
   Ensures that a particular linear variable appears once in e2 and once in e3 (rules m_lin1 and m_lin2).
   The particular linear object bound to variable will be executed once at runtime as 
   either true or false branch will be executed. *)
| ty_cond_nt : forall e1 q e2 e3 Gamma1 Gamma2 (Gamma3: typing_context) T,
               ty_expr_nt Gamma1 e1 (qty q bool_ty) ->
               ty_expr_nt Gamma2 e2 T ->
               ty_expr_nt Gamma2 e3 T ->
               context_diff Gamma1 Gamma2 Gamma3 ->
               ty_expr_nt Gamma3 (cond_expr e1 e2 e3) T
| ty_pair_nt : forall Gamma1 Gamma2 Gamma3 e1 e2 T1 T2 q,
               ty_expr_nt Gamma1 e1 T1 ->
               ty_expr_nt Gamma2 e2 T2 ->
               pred_ty q T1 ->
               pred_ty q T2 ->
               context_split Gamma1 Gamma2 Gamma2 ->
               ty_expr_nt Gamma3 (pair_expr q e1 e2) (qty q (pair_ty T1 T2))
| ty_split_nt : forall Gamma1 Gamma2 Gamma3 q e1 t1 t2 x y T1 T2 e2 T,
                ty_expr_nt Gamma1 e1 (qty q (pair_ty t1 t2)) ->
                ty_expr_nt (Gamma2 ++ [:: (x, T1)] ++ [:: (y, T2)]) e2 T ->
                context_split Gamma1 Gamma2 Gamma3 ->
                ty_expr_nt Gamma3 (split_expr e1 (var_expr x) (var_expr y) e2) T 
| ty_abs_nt : forall x e q Gamma T1 T2,
              pred_context q Gamma -> 
              ty_expr_nt (Gamma ++ [:: (x, T1)]) e T2 ->
              ty_expr_nt Gamma (abs_expr q x T1 e) (qty q (arrow_ty T1 T2))
| ty_app_nt : forall e1 e2 Gamma1 Gamma2 Gamma3 T1 T2 q,
              ty_expr_nt Gamma1 e1 (qty q (arrow_ty T1 T2)) ->
              ty_expr_nt Gamma2 e2 T1 ->
              context_split Gamma1 Gamma2 Gamma3 ->
              ty_expr_nt Gamma3 (app_expr e1 e2) T2.

(**** Deterministic Typing rules ****)
(* The relation also returns left-over context along with the type *) 
Inductive ty_expr : typing_context -> expr -> ty -> typing_context -> Prop :=
| ty_uvar : forall x T Gamma1 Gamma2, 
           ty_expr (Gamma1 ++ [:: (x, (qty un T))] ++ Gamma2) (var_expr x) (qty un T) 
           (Gamma1 ++ [:: (x, (qty un T))] ++ Gamma2)
| ty_lvar : forall x T Gamma1 Gamma2, 
           ty_expr (Gamma1 ++ [:: (x, (qty lin T))] ++ Gamma2) (var_expr x) (qty lin T) 
           (Gamma1 ++ Gamma2)
| ty_bool : forall q b Gamma,
            ty_expr Gamma (bool_expr q b) (qty q bool_ty) Gamma
| ty_cond : forall e1 q e2 e3 Gamma1 Gamma2 Gamma3 T,
            ty_expr Gamma1 e1 (qty q bool_ty) Gamma2 ->
            ty_expr Gamma2 e2 T Gamma3 ->
            ty_expr Gamma2 e3 T Gamma3 ->
            ty_expr Gamma1 (cond_expr e1 e2 e3) T Gamma3
| ty_pair : forall Gamma1 Gamma2 Gamma3 e1 e2 T1 T2 q,
            ty_expr Gamma1 e1 T1 Gamma2 ->
            ty_expr Gamma2 e2 T2 Gamma3 ->
            pred_ty q T1 ->
            pred_ty q T2 ->
            ty_expr Gamma1 (pair_expr q e1 e2) (qty q (pair_ty T1 T2)) Gamma3
| ty_split : forall Gamma1 Gamma2 Gamma3 q e1 t1 t2 x y T1 T2 e2 T,
             ty_expr Gamma1 e1 (qty q (pair_ty t1 t2)) Gamma2 ->
             ty_expr (Gamma2 ++ [:: (x, T1)] ++ [:: (y, T2)]) e2 T Gamma3 ->
             ty_expr Gamma1 (split_expr e1 (var_expr x) (var_expr y) e2) T 
             (remove_var_ty (remove_var_ty Gamma3 (x, T1)) (y, T2))
| ty_abs : forall x e q Gamma1 Gamma2 T1 T2,
           (q = un -> Gamma1 = remove_var_ty Gamma2 (x, T1)) ->
           ty_expr (Gamma1 ++ [:: (x, T1)]) e T2 Gamma2 ->
           ty_expr Gamma1 (abs_expr q x T1 e) (qty q (arrow_ty T1 T2)) (remove_var_ty Gamma2 (x, T1))
| ty_app : forall e1 e2 Gamma1 Gamma2 Gamma3 T1 T2 q,
           ty_expr Gamma1 e1 (qty q (arrow_ty T1 T2)) Gamma2 ->
           ty_expr Gamma2 e2 T1 Gamma3 ->
           ty_expr Gamma1 (app_expr e1 e2) T2 Gamma3.

(***** Operational Semantics *****)
Inductive prevalue : Type :=
| bool_val : bool -> prevalue
| pair_val : expr -> expr -> prevalue
| abs_val : string -> ty -> expr -> prevalue.

Definition value : Type := (qual * prevalue).

(* ??? *)
Inductive ty_value : typing_context -> qual -> prevalue -> ty -> Prop :=
| ty_bool_val : forall Gamma q b,
                ty_expr Gamma (bool_expr q b) (qty q bool_ty) Gamma ->
                ty_value Gamma q (bool_val b) (qty q bool_ty)
| ty_pair_val : forall Gamma Gamma' q e1 e2 T1 T2,
                ty_expr Gamma (pair_expr q e1 e2) (qty q (pair_ty T1 T2)) Gamma' ->
                ty_value Gamma q (pair_val e1 e2) (qty q (pair_ty T1 T2))
| ty_abs_val : forall Gamma Gamma' q x T1 T2 e,
               ty_expr Gamma (abs_expr q x T1 e) (qty q (arrow_ty T1 T2)) (remove_var_ty Gamma' (x, T1)) ->
               ty_value Gamma q (abs_val x T1 e) (qty q (arrow_ty T1 T2)).
                
(* Map from string to values *)
Definition state := list (string * value). 

(* Auxiliary function *)
(* To justify how unrestricted and linear variables are allocated and deallocated *)
Inductive qual_state_rel : state -> qual -> string -> state -> Prop :=
(* it ensures that the updated state does not contain the linear variable as it will
   be deallocated after its use *)
| state_qual_lin : forall s1 x v s2,
                   qual_state_rel (s1 ++ [:: (x, v)] ++ s2) 
                                  lin x (s1 ++ s2)
(* it ensures that if the variable is unrestricted the updated state remains the same
   as it is not deallocated *)
| state_qual_un : forall s x,
                  qual_state_rel s un x s.

(* Substitution *)
Fixpoint subst (x : string) (e' : expr) (e : expr) : expr :=
match e with 
| var_expr y => if String.eqb x y then e' else e 
| bool_expr q b => bool_expr q b
| cond_expr e1 e2 e3 => cond_expr (subst x e' e1) (subst x e' e2) (subst x e' e3)
| pair_expr q e1 e2 => pair_expr q (subst x e' e1) (subst x e' e2)
| split_expr e1 e2 e3 e4 => split_expr (subst x e' e1) (subst x e' e2) 
                            (subst x e' e3) (subst x e' e4)
| abs_expr q y t e => abs_expr q x t (if String.eqb y x then e else (subst x e' e))
| app_expr e1 e2 => app_expr (subst x e' e1) (subst x e' e2)
end.

(* Semantics *)
Inductive sem_expr : state -> expr -> state -> expr -> Prop :=
| e_bool : forall s x q b,
           sem_expr s (bool_expr q b) (s ++ [:: (x, (q, bool_val b))]) (var_expr x)
| e_if_true : forall (s: state) x e2 e3 q s',
              List.In (x,(q, bool_val true)) s ->
              qual_state_rel s q x s' ->
              sem_expr s (cond_expr (var_expr x) e2 e3) s' e2
| e_if_false : forall s x e2 e3 q s',
               List.In (x,(q, bool_val false)) s ->
               qual_state_rel s q x s' ->
               sem_expr s (cond_expr (var_expr x) e2 e3) s' e3
| e_pair : forall s x q y z,
           sem_expr s (pair_expr q y z) (s ++ [:: (x, (q, (pair_val y z)))]) 
           (var_expr x)
| e_split : forall s x y z e y1 z1 q s',
            List.In (x, (q, (pair_val y1 z1))) s ->
            qual_state_rel s q x s' ->
            sem_expr s (split_expr (var_expr x) (var_expr y) (var_expr z) e)
            s' (subst z z1 (subst y y1 e))
| e_fun : forall s q x t e,
          sem_expr s (abs_expr q x t e) (s ++ [:: (x, (q, (abs_val x t e)))]) (var_expr x).

(* ?? *)
Inductive ty_state : state -> typing_context -> Prop :=
| ty_emptys : ty_state nil nil 
| ty_nextlins : forall (Gamma1 Gamma2 Gamma3 : typing_context) s w T x,
                context_split Gamma1 Gamma2 Gamma3 ->
                ty_state s Gamma3 ->
                ty_value Gamma1 lin w T ->
                ty_state (s ++ [:: (x, (lin, w))]) (Gamma2 ++ [:: (x, T)])
| ty_nextuns : forall Gamma1 Gamma2 Gamma3 s w T x,
                context_split Gamma1 Gamma2 Gamma3 ->
                ty_state s Gamma3 ->
                ty_value Gamma1 un w T ->
                ty_state (s ++ [:: (x, (un, w))]) (Gamma2 ++ [:: (x, T)]).

Inductive ty_prog : typing_context -> state -> expr -> Prop :=
| ty_p : forall Gamma s e T Gamma',
         ty_state s Gamma ->
         ty_expr Gamma e T Gamma' ->
         ty_prog Gamma s e.



 
           


