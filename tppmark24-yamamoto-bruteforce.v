(* TPPmark2024 solution by Mitsuharu Yamamato; brute force version *)
(* Developed on Coq 8.20.0 and MathComp 2.2.0 *)
(* https://www.math.nagoya-u.ac.jp/~garrigue/tpp2024/ *)
From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

Section Problem1and2.

(* prod_tpermP in perm.v:
Lemma prod_tpermP s :
  {ts : seq (T * T) | s = \prod_(t <- ts) tperm t.1 t.2 & all dpair ts}.
 *)

Variable T : finType.

Definition prod_tperms (ts : seq (T * T)) : {perm T} :=
  \prod_(t <- ts) tperm t.1 t.2.

Definition min_tperms (s : {perm T}) : seq (T * T) :=
  [arg min_(ts < in_bseq (sval (prod_tpermP s)) | s == prod_tperms ts) size ts].

Lemma min_tpermsP (s : {perm T}) :
  s = prod_tperms (min_tperms s)
  /\ forall ts, s = prod_tperms ts -> size (min_tperms s) <= size ts.
Proof.
rewrite /min_tperms; case: arg_minnP => /=.
  by move/eqP: (s2valP (prod_tpermP s)).
move=> mts /eqP mts_prod mts_min; split=> //.
move=> ts s_prod; case: (leqP (size ts) (size (s2val (prod_tpermP s)))).
  by move=> sts_leq; apply/(mts_min (Bseq sts_leq))/eqP.
by move/ltnW; apply: leq_trans (valP mts).
Qed.

End Problem1and2.

Section Problem3and4.

(* perm_iotaP in seq.v:
Lemma perm_iotaP {s t : seq T} x0 (It := iota 0 (size t)) :
  reflect (exists2 Is, perm_eq Is It & s = map (nth x0 t) Is) (perm_eq s t).
 *)
Lemma perm_iotaP' {T : eqType} {s t : seq T} x0 (It := iota 0 (size t)) :
  perm_eq s t -> {Is | perm_eq Is It & s = map (nth x0 t) Is}.
Proof. (* copied from the proof of perm_iotaP. *)
move=> Est.
elim: t => [|x t IHt] in s It Est *.
  by rewrite (perm_small_eq _ Est) //; exists [::].
have /rot_to[k s1 Ds]: x \in s by rewrite (perm_mem Est) mem_head.
have [|Is1 eqIst1 Ds1] := IHt s1; first by rewrite -(perm_cons x) -Ds perm_rot.
exists (rotr k (0 :: map succn Is1)).
  by rewrite perm_rot /It /= perm_cons (iotaDl 1) perm_map.
by rewrite map_rotr /= -map_comp -(@eq_map _ _ (nth x0 t)) // -Ds1 -Ds rotK.
Qed.

(* tuple_permP in perm.v:
Lemma tuple_permP {T : eqType} {n} {s : seq T} {t : n.-tuple T} :
  reflect (exists p : 'S_n, s = [tuple tnth t (p i) | i < n]) (perm_eq s t).
 *)
Lemma tuple_permP' {T : eqType} {n} {s : seq T} {t : n.-tuple T} :
  perm_eq s t -> {p : 'S_n | s = [tuple tnth t (p i) | i < n]}.
Proof. (* copied from the proof of tuple_permP. *)
case: n => [|n] in t *; last have x0 := tnth t ord0.
  rewrite tuple0 => /perm_small_eq-> //.
  by exists 1; rewrite [mktuple _]tuple0.
case/(perm_iotaP' x0); rewrite size_tuple => Is eqIst ->{s}.
have uniqIs: uniq Is by rewrite (perm_uniq eqIst) iota_uniq.
have szIs: size Is == n.+1 by rewrite (perm_size eqIst) !size_tuple.
have pP i : tnth (Tuple szIs) i < n.+1.
  by rewrite -[_ < _](mem_iota 0) -(perm_mem eqIst) mem_tnth.
have inj_p: injective (fun i => Ordinal (pP i)).
  by apply/injectiveP/(@map_uniq _ _ val); rewrite -map_comp map_tnth_enum.
exists (perm inj_p); rewrite -[Is]/(tval (Tuple szIs)); congr (tval _).
by apply: eq_from_tnth => i; rewrite tnth_map tnth_mktuple permE (tnth_nth x0).
Qed.

Variable T : eqType.
Variable f : seq T -> seq T.
Hypothesis perm_f : forall s : seq T, perm_eq (f s) s.

Definition perm_of_fun (s : seq T) : 'S_(size s) :=
  (sval (tuple_permP' (perm_f (in_tuple s))))^-1.

Definition aperms (s : seq T) (p : 'S_(size s)) : seq T :=
  [tuple tnth (in_tuple s) (p^-1 i) | i < size s].

Arguments aperms s : clear implicits.

Lemma aperms_perm_of_fun s : aperms s (perm_of_fun s) = f s.
Proof. by rewrite /aperms invgK -(svalP (tuple_permP' _)). Qed.

Definition min_tperms_of_fun (s : seq T) : seq ('I_(size s) * 'I_(size s)) :=
  min_tperms [arg min_(p < perm_of_fun s | aperms s p == f s)
                size (min_tperms p)].

Lemma min_tperms_of_funP (s : seq T) :
  aperms s (prod_tperms (min_tperms_of_fun s)) = f s
  /\ forall ts : seq ('I_(size s) * 'I_(size s)),
      aperms s (prod_tperms ts) = f s
      -> size (min_tperms_of_fun s) <= size ts.
Proof.
rewrite /min_tperms_of_fun; case: arg_minnP => /=.
  by rewrite aperms_perm_of_fun.
move=> mp /eqP mp_sort mp_min; split; first by rewrite -(min_tpermsP _).1.
by move=> ts /eqP /mp_min /leq_trans-> //; rewrite (min_tpermsP _).2.
Qed.

(* Alternatively,
Definition min_tperms_of_fun (s : seq T) : seq ('I_(size s) * 'I_(size s)) :=
  [arg min_(ts < in_bseq (min_tperms (perm_of_fun s))
           | aperms (prod_tperms ts) == f s)
     size ts].

Lemma min_tperms_of_funP (s : seq T) :
  aperms (prod_tperms (min_tperms_of_fun s)) = f s
  /\ forall ts : seq ('I_(size s) * 'I_(size s)),
      aperms (prod_tperms ts) = f s
      -> size (min_tperms_of_fun s) <= size ts.
Proof.
rewrite /min_tperms_of_fun; case: arg_minnP => /=.
  by rewrite -(min_tpermsP _).1 aperms_perm_of_fun.
move=> mts /eqP as_mts min_mts; split=> // ts ap_ts.
case: (leqP (size ts) (size (min_tperms (perm_of_fun s)))) => [sts_leq|].
  by apply/(min_mts (Bseq sts_leq))/eqP.
by move/ltnW; apply: leq_trans (valP mts).
Qed.
*)

End Problem3and4.

Arguments aperms [T] s.

Section Problem3and4Sort.

Definition min_tperms_of_sort (s : seq nat) : seq ('I_(size s) * 'I_(size s)) :=
  min_tperms_of_fun (fun s => permEl (perm_sort leq s)) s.

Lemma min_tperms_of_sortP (s : seq nat) :
  aperms s (prod_tperms (min_tperms_of_sort s)) = sort leq s
  /\ forall ts : seq ('I_(size s) * 'I_(size s)),
      aperms s (prod_tperms ts) = sort leq s
      -> size (min_tperms_of_sort s) <= size ts.
Proof. exact: min_tperms_of_funP. Qed.

End Problem3and4Sort.
