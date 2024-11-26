(* TPPmark2024 solution by Mitsuharu Yamamato *)
(* Developed on Coq 8.20.0 and MathComp 2.2.0 *)
(* https://www.math.nagoya-u.ac.jp/~garrigue/tpp2024/ *)
From mathcomp Require Import all_ssreflect all_fingroup.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GroupScope.

(* Compared with the brute force version, this one contains the
   following improvements:
   - For Problem 1 and 2, we show that the algorithm used in
     prod_tpermP actually gives an optimal sequence of transpositions.
   - For Problem 3, we show that the sorting permutation is unique.
   - For Problem 4, we shrink the searched space from (size s)`!
     permutations to \prod_(x <- undup s) (count_mem x s)`! ones.  *)

(* Note that Problem 4 is NP-hard:
   Amihood Amir, Tzvika Hartman, Oren Kapah, Avivit Levy, and Ely Porat.
   On the Cost of Interchange Rearrangement in Strings.
   SIAM Journal on Computing, 39(4):1444-1461, 2010.
   https://doi.org/10.1137/080712969 *)

Section Problem1and2.

Variable T : finType.

Definition prod_tperms (ts : seq (T * T)) : {perm T} :=
  \prod_(t <- ts) tperm t.1 t.2.

Lemma tperm3 (x y z : T) :
  x != y -> x != z -> y != z -> tperm x y * tperm x z = tperm z y * tperm x y.
Proof.
move=> nxy nxz nyz; apply/permP => w; rewrite !permM.
case: (tpermP x y w) => [->|->|/nesym/eqP nxw /nesym/eqP nyw].
  by rewrite tpermD // 1?eq_sym // [tperm z y x]tpermD ?tpermL // 1?eq_sym.
  by rewrite tpermL tpermR tpermD.
move: nxw; case: tpermP => [->|->|_ /nesym/eqP nzw nxw]; rewrite ?eqxx //.
  by rewrite tpermL tpermR.
by rewrite !tpermD.
Qed.

Lemma tpermM_defer (x y z w : T) :
  exists y' z' w', tperm x y * tperm z w = tperm z' w' * tperm x y'
                   /\ tperm z' w' x = x.
Proof.
case: (eqVneq z w) => [<-|ne_zw].
  by exists y, z, z; rewrite !tperm1 mulg1 mul1g perm1.
case: (eqVneq x y) => [<-|ne_xy].
  case: (eqVneq z x) => [->|ne_zx]; first by exists w, x, x; rewrite tpermL.
  case: (eqVneq w x) => [->|ne_wx].
    by exists z, x, x; rewrite tpermL [tperm z x]tpermC.
  by exists x, z, w; rewrite !tperm1 mulg1 mul1g tpermD.
case: (eqVneq (tperm x y) (tperm z w)) => [->|ne_xy_zw].
  by exists x, x, x; rewrite !tperm2 tpermL; split.
case: (boolP [disjoint [set x; y] & [set z; w]]) => [dis|ndis].
  exists y, z, w; rewrite (perm_onC (tperm_on _ _) (tperm_on _ _)) //.
  split; rewrite ?tpermD //; apply: contraTneq dis => <-.
    by rewrite -setI_eq0; apply/set0Pn; exists z; rewrite inE !set21.
  by rewrite -setI_eq0; apply/set0Pn; exists w; rewrite inE set21 set22.
wlog/set2P[e_zx|e_zy]: z w ne_zw ne_xy_zw ndis / z \in [set x; y].
  move: (ndis); rewrite disjoint_sym -setI_eq0 => /set0Pn [x0].
  rewrite 4!inE => /andP [] /orP [/eqP-> z_in|/eqP-> w_in]; first by apply.
  by move/(_ w z); rewrite eq_sym ![tperm w z]tpermC [[set w; z]]setUC; apply.
  exists y, w, y; rewrite e_zx in ne_zw *; rewrite tperm3 => //; last first.
    by apply: contraNneq ne_xy_zw => ->; rewrite e_zx.
  by split=> //; rewrite tpermD => //; rewrite eq_sym.
exists w, w, y; rewrite e_zy in ne_zw *; rewrite [tperm y w]tpermC.
have ne_xw: x != w by apply: contraNneq ne_xy_zw => ->; rewrite e_zy tpermC.
rewrite -tperm3 1?eq_sym // [tperm w x]tpermC; split=> //.
by rewrite tpermD // eq_sym.
Qed.

Lemma min_prod_tpermPaux (x : T) (ts : seq (T * T)) (s := prod_tperms ts) :
  s x != x ->
  exists2 ts', tperm x (s^-1 x) * s = prod_tperms ts' & (size ts').+1 = size ts.
Proof.
elim: ts => [|t ts IHts] in s *.
  by rewrite /s /prod_tperms big_nil perm1 eqxx.
rewrite {1}/prod_tperms big_cons -/(prod_tperms _) in s * => s_x.
case: (eqVneq (tperm x (s^-1 x)) (tperm t.1 t.2)) => [->|ne_tp].
  by exists ts => //; rewrite mulgA tperm2 mul1g.
have: (tperm x (s^-1 x) * s) x = x by rewrite permM tpermL permKV.
rewrite mulgA; have [y [z [w [-> x_fp]]]] := tpermM_defer x (s^-1 x) t.1 t.2.
rewrite !permM x_fp tpermL => /(canRL (permK _))->; rewrite -mulgA.
case: IHts => [|ts' -> /= <-]; last first.
  by exists ((z, w) :: ts') => //; rewrite /prod_tperms big_cons.
apply: contraNneq ne_tp; have: s (s^-1 x) = x by rewrite permKV.
rewrite permM => {2}<- /perm_inj.
case: tpermP => [-> ->|-> ->|_ _ e_xsVx] //; first by rewrite tpermC.
by move: s_x; rewrite {1}e_xsVx permKV eqxx.
Qed.

(* prod_tpermP in perm.v:
Lemma prod_tpermP s :
  {ts : seq (T * T) | s = \prod_(t <- ts) tperm t.1 t.2 & all dpair ts}.
 *)
Lemma min_prod_tpermP s :
  {ts : seq (T * T) | [/\ s = prod_tperms ts, all dpair ts &
                       forall ts', s = prod_tperms ts' -> size ts <= size ts']}.
Proof.
have [n] := ubnP #|[pred x | s x != x]|; elim: n s => // n IHn s /ltnSE-le_s_n.
case: (pickP (fun x => s x != x)) => [x s_x | s_id]; last first.
  exists nil; split; rewrite // /prod_tperms big_nil; apply/permP=> x.
  by apply/eqP/idPn; rewrite perm1 s_id.
have [|ts [def_s ne_ts min_ts]] := IHn (tperm x (s^-1 x) * s).
  rewrite (cardD1 x) !inE s_x in le_s_n; apply: leq_ltn_trans le_s_n.
  apply: subset_leq_card; apply/subsetP=> y.
  rewrite !inE permM permE /= -(canF_eq (permK _)).
  have [-> | ne_yx] := eqVneq y x; first by rewrite permKV eqxx.
  by case: (s y =P x) => // -> _; rewrite eq_sym.
exists ((x, s^-1 x) :: ts); split.
  by rewrite /prod_tperms big_cons -/(prod_tperms _) -def_s mulgA tperm2 mul1g.
  by rewrite /= -(canF_eq (permK _)) s_x.
(* the above part is mostly copied from the proof of prod_tpermP. *)
move=> ts' s_ts'; move: s_x; rewrite s_ts' => /min_prod_tpermPaux [ts''].
by rewrite -s_ts' => /min_ts /[swap]<-.
Qed.

Definition min_tperms (s : {perm T}) : seq (T * T) :=
  sval (min_prod_tpermP s).

Lemma min_tpermsP (s : {perm T}) :
  s = prod_tperms (min_tperms s)
  /\ forall ts, s = prod_tperms ts -> size (min_tperms s) <= size ts.
Proof. by rewrite /min_tperms; case: (svalP (min_prod_tpermP s)). Qed.

End Problem1and2.

Section Problem3.

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

Section Uniq.

Variable s : seq T.
Hypothesis uniq_s : uniq s.

(* right_injective cannot be used here because the 2nd argument type
   of aperms depends on its 1st argument value. *)
Lemma apermsI_uniq (p q : 'S_(size s)) : aperms s p = aperms s q -> p = q.
Proof.
move/val_inj=> ap_eq; apply/invg_inj/permP=> i.
move/(congr1 (fun t => tnth t i)): ap_eq; rewrite !tnth_mktuple.
by move: uniq_s; rewrite -{1}[s]in_tupleE => /tuple_uniqP; apply.
Qed.

Definition min_tperms_of_fun_uniq : seq ('I_(size s) * 'I_(size s)) :=
  min_tperms (perm_of_fun s).

Lemma min_tperms_of_fun_uniqP :
  aperms s (prod_tperms min_tperms_of_fun_uniq) = f s
  /\ forall ts : seq ('I_(size s) * 'I_(size s)),
      aperms s (prod_tperms ts) = f s
      -> size min_tperms_of_fun_uniq <= size ts.
Proof.
split; first by rewrite -(min_tpermsP _).1 aperms_perm_of_fun.
move=> ts; rewrite -aperms_perm_of_fun => /apermsI_uniq.
by rewrite /min_tperms_of_fun_uniq => <-; apply: (min_tpermsP _).2.
Qed.

End Uniq.

End Problem3.

Arguments aperms [T] s.

Section Problem4.

Section APermT.

Variables (n : nat) (T : Type).

Definition apermt (t : n.-tuple T) (p : 'S_n) : n.-tuple T :=
  [tuple tnth t (p^-1 i) | i < n].

Lemma tnth_apermt (t : n.-tuple T) (p : 'S_n) (i : 'I_n) :
  tnth (apermt t p) i = tnth t (p^-1 i).
Proof. by rewrite tnth_mktuple. Qed.

Lemma apermt1 t : apermt t 1 = t.
Proof. by apply: eq_from_tnth => ?; rewrite tnth_apermt invg1 perm1. Qed.

Lemma apermtM t p q : apermt t (p * q) = apermt (apermt t p) q.
Proof. by apply: eq_from_tnth => i; rewrite !tnth_apermt invMg permM. Qed.

Canonical permt_action := TotalAction apermt1 apermtM.

End APermT.

Prenex Implicits apermt.

Variables (n : nat) (T : finType).

Lemma astab1_apermt (t : n.-tuple T) :
  'C[t | apermt] = \prod_x Sym [set i | tnth t i == x].
Proof.
apply/setP=> /= p; apply/astab1P/prodsgP => /= [t_p|]; last first.
  case=> c in_sym {p}->; elim/big_ind: _; first by rewrite act1.
    by move=> ? ?; rewrite actM /= => ->.
  move=> x _; apply: eq_from_tnth => i; rewrite tnth_apermt.
  move/(_ x isT): in_sym; rewrite inE => perm_on_cx.
  case: (boolP (i \in [set i0 | tnth t i0 == x])) => [i_in|i_nin]; last first.
    by rewrite (out_perm (perm_onV perm_on_cx) i_nin).
  move/im_perm_on/setP/(_ i): perm_on_cx; rewrite i_in; case/imsetP => i'.
  by move: i_in; rewrite !inE => /eqP-> /eqP t_i' ->; rewrite permK.
exists (fun x => restr_perm [set i | tnth t i == x] p) => [i _|].
  by rewrite inE restr_perm_on.
apply/permP => i; rewrite -big_filter; have [e _ [Ue mem_e] _] := big_enumP.
pose x := tnth t i; case/splitPr: (mem_e x) Ue => e1 e2; rewrite uniq_catC.
rewrite cat_cons cons_uniq mem_cat negb_or => /andP[/andP[x_ne2 x_ne1] _].
rewrite big_cat big_cons /= !permM [in RHS](_ : _ i = i); last first.
  elim: e1 => [|y e1 IHe1] in x_ne1 *; first by rewrite big_nil perm1.
  move: x_ne1; rewrite inE negb_or => /andP[x_ne_y x_ne1].
  by rewrite big_cons permM (out_perm (restr_perm_on _ _)) ?IHe1 // inE.
rewrite restr_permE; last first; first by rewrite inE.
  by apply/astabsP=> j; rewrite !inE /= -{1}t_p tnth_apermt permK.
elim: e2 => [|y e2 IHe2] in x_ne2 *; first by rewrite big_nil perm1.
move: x_ne2; rewrite inE negb_or => /andP[x_ne_y x_ne2].
rewrite big_cons permM (out_perm (restr_perm_on _ _)); first by apply: IHe2.
by rewrite inE -t_p tnth_apermt permK.
Qed.

Lemma amove_apermt (t : n.-tuple T) (p : 'S_n) :
  amove apermt [set: 'S_n] t (apermt t p)
  = \prod_x Sym [set i | tnth t i == x] :* p.
Proof. by rewrite amove_act ?subxx ?inE // astabIdom astab1_apermt. Qed.

Definition min_tperms_of_apermt (t : n.-tuple T) (p : 'S_n)
  : seq ('I_n * 'I_n) :=
  min_tperms [arg min_(q < p in \prod_x Sym [set i | tnth t i == x] :* p)
                size (min_tperms q)].

Lemma min_tperms_of_apermtP (t : n.-tuple T) (p : 'S_n) :
  apermt t (prod_tperms (min_tperms_of_apermt t p)) = apermt t p
  /\ forall ts : seq ('I_n * 'I_n),
      apermt t (prod_tperms ts) = apermt t p
      -> size (min_tperms_of_apermt t p) <= size ts.
Proof.
rewrite /min_tperms_of_apermt; case: arg_minnP => /=.
  by rewrite -astab1_apermt; apply/mulsgP; exists 1 p; rewrite ?set11 ?mul1g.
move=> q q_in q_min; split=>[|ts tts_tp].
  by move: q_in; rewrite -amove_apermt !inE -(min_tpermsP _).1 => /eqP.
have: prod_tperms ts \in amove apermt [set: 'S_n] t (apermt t p).
  by rewrite !inE /= tts_tp.
by rewrite amove_apermt => /q_min /leq_trans-> //; rewrite (min_tpermsP _).2.
Qed.

End Problem4.

Section Problem3Sort.

Definition min_tperms_of_sort_uniq (s : seq nat)
  : seq ('I_(size s) * 'I_(size s)) :=
  min_tperms_of_fun_uniq (fun s => permEl (perm_sort leq s)) s.

Lemma min_tperms_of_sort_uniqP (s : seq nat) :
  uniq s ->
  aperms s (prod_tperms (min_tperms_of_sort_uniq s)) = sort leq s
  /\ forall ts : seq ('I_(size s) * 'I_(size s)),
      aperms s (prod_tperms ts) = sort leq s
      -> size (min_tperms_of_sort_uniq s) <= size ts.
Proof. exact: min_tperms_of_fun_uniqP. Qed.

End Problem3Sort.

Section Problem4Sort.

Section InSubSeqTuple.

Variable T : eqType.

Definition in_sub_seq_tuple (s : seq T) : (size s).-tuple (seq_sub s).
case: s => [|x s]; first by apply: [tuple].
exists (map (in_sub_seq (isT : 0 < size (x :: s))) (x :: s)).
by rewrite -(size_map val) -seq_subE.
Defined.

Lemma in_sub_seq_tupleE (s : seq T) : s = map val (in_sub_seq_tuple s).
Proof. by case: s => // ? ?; rewrite -seq_subE. Qed.

Lemma apermt_in_sub_seq_tuple (s : seq T) (p : {perm 'I_(size s)}) :
  aperms s p = map val (apermt (in_sub_seq_tuple s) p).
Proof.
congr val; apply: eq_from_tnth => i; rewrite tnth_mktuple tnth_map tnth_apermt.
rewrite -[RHS]tnth_map; congr tnth; apply: val_inj.
by rewrite /= -in_sub_seq_tupleE.
Qed.

End InSubSeqTuple.

Definition min_tperms_of_sort (s : seq nat) : seq ('I_(size s) * 'I_(size s)) :=
  min_tperms_of_apermt (in_sub_seq_tuple s)
    (perm_of_fun (fun s => permEl (perm_sort leq s)) s).

Lemma min_tperms_of_sortP (s : seq nat) :
  aperms s (prod_tperms (min_tperms_of_sort s)) = sort leq s
  /\ forall ts : seq ('I_(size s) * 'I_(size s)),
      aperms s (prod_tperms ts) = sort leq s
      -> size (min_tperms_of_sort s) <= size ts.
Proof.
rewrite /min_tperms_of_sort; split=> [|ts].
  rewrite apermt_in_sub_seq_tuple (min_tperms_of_apermtP _ _).1.
  by rewrite -apermt_in_sub_seq_tuple aperms_perm_of_fun.
rewrite -(aperms_perm_of_fun (fun s => permEl (perm_sort leq s))).
rewrite !apermt_in_sub_seq_tuple => /(inj_map val_inj) /val_inj.
exact: (min_tperms_of_apermtP _ _).2.
Qed.

End Problem4Sort.
