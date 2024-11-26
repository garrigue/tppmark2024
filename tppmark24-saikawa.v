From mathcomp Require Import all_ssreflect all_algebra all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.Theory.
Local Open Scope group_scope.


Section minimal_decomp.
Variable (T : finType) (s : {perm T}).

Definition is_decomp : {pred seq (T * T)} :=
  fun ts => (s == \prod_(t <- ts) tperm t.1 t.2) && (all dpair ts).

Definition is_decomp_tuple n : {pred (n.-tuple (T * T))} :=
  fun ts => is_decomp (\val ts).
 
Definition exists_decomp_tuple : {pred nat} :=
  fun n => [exists ts : n.-tuple (T * T), is_decomp_tuple ts].

Definition is_minimal_decomp (ts : seq (T * T)) :=
  is_decomp ts /\ (forall ts', is_decomp ts' -> size ts <= size ts').

Lemma exists_minimal_decomp : {ts : seq (T * T) | is_minimal_decomp ts}.
Proof.
rewrite /is_minimal_decomp.
have [ts0 ts0_decomp ts0_noloop] := prod_tpermP s.
have edt_n: exists n, exists_decomp_tuple n.
  exists (size ts0); apply/existsP=> /=; exists (in_tuple ts0).
  by rewrite /is_decomp_tuple /= /is_decomp ts0_decomp ts0_noloop eqxx.
have[m]:= ex_minnP edt_n.
case/existsP/sigW=> /= ts; rewrite /is_decomp_tuple=> /= ts_decomp ts_min.
exists ts; rewrite ts_decomp; split=>// ts' ts'_decomp.
rewrite size_tuple; apply: ts_min.
by apply/existsP=> /=; exists (in_tuple ts').
Defined.

End minimal_decomp.


Section problem12.
Variable (T : finType).

Definition Problem1 (s : {perm T}) : seq (T * T) := sval (exists_minimal_decomp s).

Lemma Problem2 (s : {perm T}) : is_minimal_decomp s (Problem1 s).
Proof.
by rewrite /is_minimal_decomp /Problem1; case: exists_minimal_decomp=> ts.
Qed.

End problem12.


(* [tuple tnth t (p i) | i < n] is the action of a permutation p on a tuple t *)
Definition tuple_perm {T : eqType} {n : nat}
  (t : n.-tuple T) (p : {perm 'I_n}) := [tuple tnth t (p i) | i < n].
Notation "t @ p" := (tuple_perm t p) (at level 10).


Section perm_ext.
Lemma tuple_perm_eqE {T : eqType} {n : nat} {s : seq T} {t : n.-tuple T} :
  (perm_eq s t) = [exists p : {perm 'I_n}, s == t @ p] .
Proof.
apply/idP/idP; rewrite -(rwP tuple_permP).
  by case=> p Hp; apply/existsP; exists p; rewrite Hp.
by case/existsP=> p Hp; exists p; apply/eqP.
Qed.
End perm_ext.


Section exists_tuple_sorting_perm.
Variable (d : unit) (T : orderType d) (n : nat) (s : n.-tuple T).

(* T *l 'I_n = T * 'I_n with the standard lexicographic order *)
Let sn := [tuple (tnth s i, i) | i < n] : n.-tuple (T *l 'I_n).

Let uniq_sn : uniq sn.
Proof.
by apply/tuple_uniqP=> x y /(congr1 snd); rewrite !tnth_mktuple.
Qed.

Let exists_sn_sorting_perm :
  {p : {perm 'I_n} | sorted <=%O (sn @ p)}.
Proof.
have:= mem_sort <=%O sn.
move/uniq_perm; rewrite sort_uniq uniq_sn=> /(_ erefl erefl).
rewrite tuple_perm_eqE; case/existsP/sigW=> p /eqP sort_snE.
exists p; rewrite -sort_snE sort_sorted=> //.
exact: le_total.
Defined.

Lemma exists_tuple_sorting_perm :
  {p : {perm 'I_n} | sorted <=%O (s @ p)}.
Proof.
have[p Hp]:= exists_sn_sorting_perm; exists p.
have: {homo (fun xi : T *l 'I_n=> fst xi) : x y / <=%O x y >-> <=%O x y}.
  by move=> [??] [??] /=; rewrite lexi_pair=> /andP [].
move/homo_sorted/(_ (sn @ p) Hp).
suff->: [seq xi.1 | xi <- sn @ p] = s @ p by [].
rewrite -map_comp.
by under eq_map=>i do rewrite /sn /= tnth_mktuple /=.
Defined.

End exists_tuple_sorting_perm.


Section problem34.
Variable (d : unit) (T : orderType d).

Theorem Problem4_proof (n : nat) (s : n.-tuple T) :
  {ts : seq ('I_n * 'I_n) |
    let p := \prod_(t <- ts) tperm t.1 t.2 in
    sorted <=%O (s @ p) /\ is_minimal_decomp p ts}.
Proof.
exists (Problem1 (sval (exists_tuple_sorting_perm s))).
move=> p; have->: p = sval (exists_tuple_sorting_perm s).
  rewrite /p; case: exists_tuple_sorting_perm=> q /= _.
  rewrite /Problem1; case: exists_minimal_decomp=> ts /=.
  rewrite /is_minimal_decomp=> -[] /[swap] _.
  by rewrite /is_decomp=> /andP [] /eqP <-.
split; last exact: Problem2.
by case: exists_tuple_sorting_perm.
Defined.

Definition Problem4 (n : nat) (s : n.-tuple T) := sval (Problem4_proof s).

Corollary Problem3_Proof (n : nat) (s : n.-tuple T) :
  uniq s ->
  {ts : seq ('I_n * 'I_n) |
    let p := \prod_(t <- ts) tperm t.1 t.2 in
    sorted <=%O (s @ p) /\ is_minimal_decomp p ts}.
Proof. by move=>?; exact: Problem4_proof. Defined.

Definition Problem3 := Problem4.

End problem34.


Section experiments.

Local Close Scope group_scope.

Definition P4_nat := @Problem4 _ nat.

Let t1 := [tuple 1].
Check P4_nat t1 : seq ('I_1 * 'I_1).

Fail Timeout 3 Compute P4_nat t1.
End experiments.
