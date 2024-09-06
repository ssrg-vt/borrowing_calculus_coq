From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat eqtype div ssralg seq.
Require Import String ZArith Coq.Structures.OrderedTypeEx expr.

Lemma unrestricted_lin : forall Gamma1 x T Gamma2,
  unrestricted_part (append_context (extend_context Gamma1 x (qty lin T)) Gamma2) =
  unrestricted_part (append_context Gamma1 Gamma2).
Proof.
Admitted.

Lemma subset_append_linear_extend : forall Gamma1 Gamma2 x T,
subset (linear_part (append_context Gamma1 Gamma2))
       (linear_part (append_context (extend_context Gamma1 x (qty lin T)) Gamma2)).
Proof.
Admitted.

Lemma subset_trans : forall Gamma1 Gamma2 Gamma3,
subset Gamma1 Gamma2 ->
subset Gamma2 Gamma3 ->
subset Gamma1 Gamma3.
Proof.
Admitted.

Lemma subset_linear_extend : forall Gamma1 x T Gamma2,
subset (linear_part Gamma1) (linear_part (extend_context Gamma2 x T)) ->
subset (linear_part (remove_var_ty Gamma1 x T)) (linear_part Gamma2).
Proof.
Admitted.


Lemma is_unrestricted : forall Gamma x T,
unrestricted_part Gamma = [:: (x, T)] ->
check_unrestricted_ty T = true.
Proof.
move=> Gamma x T. elim: Gamma=> //= h t ih.
case: ifP=> //= hc ih'. 
case: h hc ih'=> //= x' T' ht [] heq heq' ht'. by rewrite heq' in ht.
Qed.

Lemma eq_ty_un : forall T T',
check_unrestricted_ty T = true ->
eq_ty T' T = true -> 
check_unrestricted_ty T' = true.
Proof.
move=> [] q t [] q' t' /=. case: q=> //= _.
by case: ifP=> //=.
Qed.

Lemma neq_ty_un : forall T T',
check_unrestricted_ty T = false ->
eq_ty T' T = true -> 
check_unrestricted_ty T' = false.
Proof.
move=> [] q t [] q' t' /=. case: q=> //= _.
case: ifP=> //= heq heq'. by case: q' heq=> //=.
Qed.

Lemma unrestricted_context : forall Gamma x T, 
unrestricted_part Gamma = [::] ->
unrestricted_part (remove_var_ty Gamma x T) = [::].
Proof.
move=> Gamma x T. elim: Gamma=> //= h t ih.
case: ifP=> //= hc ht. case: ifP=> //= heq.
rewrite hc /=. by apply ih.
Qed.

Lemma unrestricted_remove_empty : forall Gamma x T,
unrestricted_part (remove_var_ty Gamma x T) = [::] ->
(unrestricted_part Gamma = [::]) \/ check_unrestricted_ty T = true.
Proof.
move=> Gamma x T h. elim: Gamma h=> //= h.
+ by left.
case: h=> //= x' T'. move=> t ih. case: ifP=> //= heq.
+ move=> hu. case: ifP=> //= hc.
  + have hu' := unrestricted_context t x T hu. 
    move: (ih  hu')=> [] hh.
    + right. apply andb_prop in heq. simpl in heq. 
      case: heq=> heq1 heq2.
      by have := eq_ty_un T' T hc heq2.
    by right.
  by left.
by case: ifP=> //=.
Qed.

Lemma eq_qual_refl : forall q,
eq_qual q q.
Proof.
move=> q. by case: q=> //=.
Qed.

Lemma eq_pty_refl : forall p (h : forall t, eq_ty t t),
eq_pty p p.
Proof.
move=> p h. case: p=> //=.
+ move=> t1 t2. rewrite /andb. case: ifP=> //=.
  move=> heq. move: (h t1)=> heq'; subst. by rewrite heq' in heq.
move=> t t'. rewrite /andb. case: ifP=> //= hf. 
move: (h t)=> heq'. by rewrite heq' in hf.
Qed.

Lemma eq_qual_eq : forall t1 t2 t3,
eq_qual t1 t3 ->
eq_qual t2 t3 ->
t1 = t2.
Proof.
move=> t1 t2 t3 h1 h2. case: t3 h1 h2=> //=.
+ case: t1=> //= _. by case: t2=> //=.
case: t1=> //= _. by case: t2=> //=. 
Qed.

Lemma eq_pty_eq : forall pt1 pt2 pt3 
(h : forall t1 t2 t3, eq_ty t1 t3 -> eq_ty t2 t3 -> t1 = t2),
eq_pty pt1 pt3 ->
eq_pty pt2 pt3 ->
pt1 = pt2.
Proof.
move=> t1 t2 t3 h. elim: t3=> //=.
+ elim: t1=> //=. by elim: t2=> //=.
+ move=> tp1 tp2. elim: t1=> //= tp1' tp2'.
  rewrite /andb. case: ifP=> //=. case: t2=> //= tp1'' tp2''.
  rewrite /andb. case: ifP=> //= h1 h2 h3 h4.
  move: (h tp1'' tp1' tp1 h1 h2)=> heq; subst.
  by move: (h tp2' tp2'' tp2 h3 h4)=> heq; subst.
move=> t t'. elim: t1=> //= t1' t2'. rewrite /andb.
case: ifP=> //= ht1 ht2. case: t2=> //= t21 t22.
rewrite /andb. case: ifP=> //= h11 h12.
move: (h t1' t21 t ht1 h11)=> heq; subst.
by move: (h t2' t22 t' ht2 h12)=> heq; subst.
Qed.

Lemma eq_ty_eq : forall t1 t2 t3
(h : forall pt1 pt2 pt3, eq_pty pt1 pt3 -> eq_pty pt2 pt3 -> pt1 = pt2), 
eq_ty t1 t3 ->
eq_ty t2 t3 ->
t1 = t2.
Proof.
move=> t1 t2 t3 hpeq h h'. case: t1 h=> //= q p.
case: t3 h'=> //= q' p' h'. case: ifP=> //= hq hq'.
case: t2 h'=> //= q'' p''. case: ifP=> //= hq'' hp.
have hqeq := eq_qual_eq q q'' q' hq hq''; subst.
by move: (hpeq p p'' p' hq' hp)=> heq; subst. 
Qed.

Lemma remove_extend_refl : forall Gamma x T x' T',
x <> x' ->
(extend_context (remove_var_ty Gamma x T) x' T') = 
(remove_var_ty (extend_context Gamma x' T') x T).
Proof.
move=> Gamma x T x' T' hneq. elim: Gamma=> //=.
+ case: ifP=> //= heq. rewrite /andb in heq.
  move: heq. case: ifP=> //= heq ht. apply eqb_eq in heq.
  by rewrite heq in hneq.
move=> h t hs /=. case: ifP=> //=. 
+ rewrite /andb. case: ifP=> //= heq ht. case: ifP=> //= heq'.
  + rewrite /andb. case: ifP=> //=.
    + case: ifP=> //= heq''. apply eqb_eq in heq''. by rewrite heq'' in hneq.
    case: ifP=> //= heq'' hteq.
    + apply eqb_eq in heq''. by rewrite heq'' in hneq.
    apply eqb_eq in heq. apply eqb_eq in heq'. rewrite -heq in heq'.
    by rewrite heq' in hneq.
  by rewrite heq /= ht /=.
rewrite /andb. case: ifP=> //= heq ht.
+ case: ifP=> //= heq'.
  + apply eqb_eq in heq; subst. apply eqb_eq in heq'.
    by rewrite heq' in hneq.
  by rewrite heq /= ht /= hs.
case: ifP=> //= heq'.
+ case: ifP=> //=. rewrite /andb /=. case: ifP=> //= heq''.
  apply eqb_eq in heq''. by rewrite heq'' in hneq.
by rewrite /andb /= heq /= hs.
Qed.

Lemma extend_remove_empty : forall Gamma x T x' T',
x <> x' ->
remove_var_ty Gamma x' T' = [::] ->
remove_var_ty (extend_context Gamma x T) x' T' =  [:: (x, T)].
Proof.
move=> Gamma x T x' T' hneq. elim: Gamma=> //=.
+ rewrite /andb /=. case: ifP=> //=. case: ifP=> //= heq.
  apply eqb_eq in heq. by rewrite heq in hneq.
move=> [] a t aa ih /=. case: ifP=> //=. rewrite /andb /=.
case: ifP=> //= heq ht haa. apply eqb_eq in heq. rewrite heq /=.
rewrite heq in hneq. case: ifP=> //= heq'.
+ rewrite /andb /=. apply eqb_eq in heq'. by rewrite heq' in hneq.
rewrite /andb /=. case: ifP=> //=.
+ case: ifP=> //= haeq ht'. by rewrite haa /=.
case: ifP=> //= haeq ht'.
+ by rewrite ht in ht'.
have haeq' : (a =? a)%string. + by apply eqb_refl. 
by rewrite haeq' in haeq. 
Qed.


Lemma unrestricted_remove : forall Gamma x T,
unrestricted_part Gamma = [:: (x, T)] ->
unrestricted_part (remove_var_ty Gamma x T) = [::].
Proof.
move=> Gamma x T. elim: Gamma=> //= [] h t ih.
case: ifP=> //=.
(* head contains unrestricted *)
+ move=> /= hc ih' /=. inversion ih'; rewrite /=; subst.
  case: ifP=> //= heq. rewrite /= in hc. rewrite hc /=. 
  case: T ih ih' heq hc=> //= q p. case: q=> //= ih ih' heq hc.
  have hs : (x =? x)%string. + by apply eqb_refl. rewrite hs in heq.
  rewrite Bool.andb_true_l in heq. 
  have hp: eq_pty p p. + admit. by rewrite hp in heq.
(* tail contrains unrestricted *)
move=> hc hi /=. move: (ih hi)=> ih'. 
case: ifP=> //= heq.
+ apply unrestricted_remove_empty in ih'. 
  apply andb_prop in heq. case: heq=> heq1 heq2.
  have hneq := neq_ty_un h.2 T hc heq2. rewrite hneq /= in ih'.
  by case: ih'=> //=.
case: ifP=> //= hc'. by rewrite hc' in hc.
Admitted.

Lemma unrestricted_exchange : forall Gamma x T y T',
unrestricted_part (remove_var_ty (remove_var_ty Gamma x T) y T') = 
unrestricted_part (remove_var_ty (remove_var_ty Gamma y T') x T).
Proof.
move=> Gamma x T y T'. elim: Gamma=> //=.
move=> [] xh Th t ih /=. case: ifP=> //=.
(* at head *)
+ rewrite /andb /=. case: ifP=> //= hxeq hteq. 
  case: ifP=> //=.
  + case: ifP=> //= hyeq hteq'. apply eqb_eq in hxeq; subst.
    apply eqb_eq in hyeq; subst. case: T ih hteq=> //= q p.
    case: Th hteq'=> //= q' p' hteq'. case: ifP=> //= hq ih hpteq.
    case: T' hteq' ih=> //= q'' p''. case: ifP=> //= hq' hpteq' ih.
    case: p hpteq ih=> //=.
    + case: p' hpteq'=> //=. case: p''=> //= _ _ ih.
      by have hqeq := eq_qual_eq q q'' q' hq hq'; subst.
    move=> t1 t2. case: p' hpteq'=> //= t3 t4.
    case: p''=> //= t5 t6. rewrite /andb. case: ifP=> //= hteq hteq'.
    case: ifP=> //= hteq1 hteq1' ih. 
    have hqeq := eq_qual_eq q q'' q' hq hq'; subst. admit.
    admit.
  case: ifP=> //= heq htneq. 
  + by rewrite hxeq /= hteq /=. 
  by rewrite hxeq /= hteq /=.
rewrite /andb. case: ifP=> //= hxeq hteq.
+ case: ifP=> //=. case: ifP=> //= hyeq hteq'.
  + case: ifP=> //= hc. 
    + rewrite hxeq /= hteq /= hc /=. by rewrite ih.
    rewrite hxeq /= hteq /= hc /=. by apply ih.
  case: ifP=> //= hc.
  + rewrite hxeq /= hteq /= hc /=. by rewrite ih.
  rewrite hxeq /= hteq /= hc /=. by apply ih.
case: ifP=> //=. case: ifP=> //= hyeq hteq'.
+ case: ifP=> //= hc.
  + by rewrite hxeq /= hc /= ih.
  by rewrite hxeq /= hc /=.
case: ifP=> //= hc.
+ by rewrite hxeq /= hc /= ih.
by rewrite hxeq /= hc /=.
Admitted.

Lemma linear_exchange : forall Gamma x T y T',
linear_part (remove_var_ty (remove_var_ty Gamma x T) y T') = 
linear_part (remove_var_ty (remove_var_ty Gamma y T') x T).
Proof.
move=> Gamma x T y T'. elim: Gamma=> //=.
move=> [] xh Th t ih /=. case: ifP=> //=.
(* at head *)
+ rewrite /andb /=. case: ifP=> //= hxeq hteq. 
  case: ifP=> //=.
  + case: ifP=> //= hyeq hteq'. apply eqb_eq in hxeq; subst.
    apply eqb_eq in hyeq; subst. case: T ih hteq=> //= q p.
    case: Th hteq'=> //= q' p' hteq'. case: ifP=> //= hq ih hpteq.
    case: T' hteq' ih=> //= q'' p''. case: ifP=> //= hq' hpteq' ih.
    case: p hpteq ih=> //=.
    + case: p' hpteq'=> //=. case: p''=> //= _ _ ih.
      by have hqeq := eq_qual_eq q q'' q' hq hq'; subst.
    move=> t1 t2. case: p' hpteq'=> //= t3 t4.
    case: p''=> //= t5 t6. rewrite /andb. case: ifP=> //= hteq hteq'.
    case: ifP=> //= hteq1 hteq1' ih. 
    have hqeq := eq_qual_eq q q'' q' hq hq'; subst. admit.
    admit.
  case: ifP=> //= heq htneq. 
  + by rewrite hxeq /= hteq /=. 
  by rewrite hxeq /= hteq /=.
rewrite /andb. case: ifP=> //= hxeq hteq.
+ case: ifP=> //=. case: ifP=> //= hyeq hteq'.
  + case: ifP=> //= hc. 
    + rewrite hxeq /= hteq /= hc /=. by rewrite ih.
    rewrite hxeq /= hteq /= hc /=. by apply ih.
  case: ifP=> //= hc.
  + rewrite hxeq /= hteq /= hc /=. by rewrite ih.
  rewrite hxeq /= hteq /= hc /=. by apply ih.
case: ifP=> //=. case: ifP=> //= hyeq hteq'.
+ case: ifP=> //= hc.
  + by rewrite hxeq /= hc /= ih.
  by rewrite hxeq /= hc /=.
case: ifP=> //= hc.
+ by rewrite hxeq /= hc /= ih.
by rewrite hxeq /= hc /=.
Admitted.

Lemma unrestricted_extend : forall Gamma1 Gamma2 x T,
unrestricted_part (extend_context Gamma1 x T) = unrestricted_part Gamma2 ->
unrestricted_part Gamma1 = unrestricted_part (remove_var_ty Gamma2 x T).
Proof.
move=> Gamma1 Gamma2 x T h. elim: Gamma1 h=> [ | [] x1 T1 xxs ih] //=. 
(* nil *)
+ case: ifP=> //= heq ih.
  (* x is unrestricted variable *)
  + elim: Gamma2 ih=> //= h t ih. case: ifP=> //= hc.
    + case: ifP=> //= heq'.
      + move=> ihh. by inversion ihh. 
        move=> ihh. rewrite hc /=. 
        case: h hc heq heq' ihh=> //= y T' hc heq heq' [] heq'' heq''' h; subst.
        have hs : (y =? y)%string. + by rewrite eqb_refl.
        have ht : (eq_ty T' T'). + case: T' ih hc heq' heq=> //= q p ih hc heq heq'. 
        case: ifP=> //= hq. 
        + admit.
        by case: q hq ih hc heq heq'=> //=.
      by rewrite hs ht in heq'.
    move=> hu. case: ifP=> //=.
    + rewrite /andb. case: ifP=> //= hs hseq.
      have hc' := neq_ty_un h.2 T hc hseq.
      move: (ih hu)=> hu'. symmetry in hu'.
      have hd := unrestricted_remove_empty t x T hu'. destruct hd; auto.
      by rewrite H in hc'.
    rewrite /andb /=. case: ifP=> //= hs hseq. rewrite hc /=.
    by apply ih.
  rewrite hc /=. by apply ih.
  symmetry in ih. by have := unrestricted_context Gamma2 x T ih.
(* non-empty case *)
admit.
Admitted.
