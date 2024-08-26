From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

Definition total_map (A: Type) := string -> A.

Definition empty_map {A: Type} (v: A) : total_map A :=
  fun (_ : string) => v.

Definition extend_map {A: Type} (m: total_map A) (k: string) (v: A) : total_map A :=
  fun (x : string) => if eqb k x then v else m x.

Lemma add_to_empty : forall A x v, @empty_map A v x = v.
Proof.
move=> A x. by unfold empty_map.
Qed.

Lemma extend_eq_map : forall A (m: total_map A) x v, (extend_map m x v) x = v.
Proof.
move=> A m x v. unfold extend_map.
case: ifP=> //= heq.  have heq':= eqb_refl x. by rewrite heq in heq'.
Qed.

Lemma extend_neq_map : forall A (m: total_map A) x1 x2 v, 
x1 <> x2 ->
(extend_map m x1 v) x2 = m x2.
Proof.
move=> A m x1 x2 v hneq. unfold extend_map.
case: ifP=> //= heq. have [h1 h2]:= eqb_neq x1 x2.
move: (h2 hneq)=> h3. by rewrite h3 in heq.
Qed.

Lemma extend_shadow_map : forall A (m: total_map A) v1 v2 x,
extend_map (extend_map m x v1) x v2 = extend_map m x v2.
Proof.
move=> A m v1 v2 x. unfold extend_map.
apply functional_extensionality_dep. move=> x'.
case: ifP=> //= hneq. case: ifP=> //= hneq'.
by rewrite hneq' in hneq.
Qed.

Lemma extend_same_map : forall A (m : total_map A) x,
extend_map m x (m x) = m.
Proof.
move=> A m x. unfold extend_map.
apply functional_extensionality_dep. move=> x'.
case: ifP=> //= heq. apply f_equal. have [h1 h2] := eqb_eq x x'.
by move: (h1 heq).
Qed.

Lemma extend_permute_map : forall A (m : total_map A) v1 v2 x1 x2,
x2 <> x1 ->
(extend_map (extend_map m x2 v2) x1 v1) = (extend_map (extend_map m x1 v1) x2 v2).
Proof.
move=> A m v1 v2 x1 x2 hneq. rewrite /extend_map.
apply functional_extensionality_dep. move=> x.
case: ifP=> //= heq. case: ifP=> //= heq'.
have [h1 h2] := eqb_eq x2 x.
move: (h1 heq')=> hh; subst. have [h1' h2'] := eqb_eq x1 x.
by move: (h1' heq)=> hh'; subst. 
Qed.

Definition partial_map (A:Type) := total_map (option A).

Definition empty {A: Type} : partial_map A :=
  empty_map None.

Definition extend {A: Type} (m: partial_map A) (k: string) (v: A) :=
  extend_map m k (Some v).

Lemma get_empty : forall A x, @empty A x = None. 
Proof.
move=> A x. by rewrite /empty /empty_map.
Qed.

Lemma extend_eq : forall A (m : partial_map A) x v,
(extend m x v) x = Some v.
Proof.
move=> A m x v. rewrite /extend. by rewrite extend_eq_map.
Qed.

Lemma extend_neq : forall A (m : partial_map A) x1 x2 v,
x2 <> x1 ->
(extend m x2 v) x1 = m x1.
Proof.
move=> A m x1 x2 v hneq. rewrite /extend. by rewrite extend_neq_map.
Qed.

Lemma extend_shadow : forall A (m : partial_map A) x v1 v2,
extend (extend m x v1) x v2 = extend m x v2.
Proof.
move=> A m x v1 v2. rewrite /extend. by rewrite extend_shadow_map.
Qed.

Lemma extend_same : forall A (m: partial_map A) x v,
m x = Some v ->
extend m x v = m.
Proof.
move=> A m x v h. rewrite /extend -h. by rewrite extend_same_map.
Qed.

Lemma extend_permute : forall A (m: partial_map A) x1 x2 v1 v2,
x2 <> x1 ->
(extend (extend m x2 v2) x1 v1) =
(extend (extend m x1 v1) x2 v2).
Proof.
move=> A m x1 x2 v1 v2 hneq. rewrite /extend. rewrite extend_permute_map; auto.
Qed.






