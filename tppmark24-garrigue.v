From HB Require Import structures.
From mathcomp Require Import all_ssreflect.
From mathcomp Require boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition compr {A B C} (f : A -> B) (g : B -> C) := g \o f.
Lemma comprA {A B C D} (f : A -> B) (g : B -> C) (h : C -> D) :
  compr f (compr g h) = compr (compr f g) h.
Proof. done. Qed.
Lemma compr0f {A B} (f : A -> B) : compr id f = f. Proof. done. Qed.
Lemma comprf0 {A B} (f : A -> B) : compr f id = f. Proof. done. Qed.
Lemma comp0f {A B} (f : A -> B) : comp id f = f. Proof. done. Qed.
Lemma compf0 {A B} (f : A -> B) : comp f id = f. Proof. done. Qed.

HB.instance Definition _ T :=
  @Monoid.isLaw.Build (T -> T) id compr comprA compr0f comprf0.

HB.instance Definition _ T :=
  @Monoid.isLaw.Build (T -> T) id comp compA comp0f compf0.

Section finset.
Variables (T I : finType) (P : pred I) (F :  I -> T) (G : I -> {set T}).
Lemma imset_bigcup : [set F x | x in P] = \bigcup_(x in P) [set F x].
Proof.
apply/setP => x.
apply/imsetP.
case: ifP.
- case/bigcupP => i Hi. rewrite inE => /eqP xi. by exists i.
- apply: contraFnot => -[i Hi ->].
  apply/bigcupP. exists i => //. by rewrite inE.
Qed.

Lemma bigcup_same i :
  (forall j, P j -> G i = G j) -> P i -> \bigcup_(j in P) G j = G i.
Proof.
move=> HG Pi; apply/setP => x; apply/bigcupP.
case: ifP => xS; by [exists i | case=> j /HG <-; rewrite xS].
Qed.

Lemma setseqP (s1 s2 : seq T) :
  s1 =i s2 <-> [set:: s1] = [set:: s2].
Proof.
split=> [| /setP] H.
  by apply/setP => x; rewrite !inE.
by move=> x; move/(_ x): H; rewrite !inE.
Qed.

Lemma set_cat (s1 s2 : seq T) :
  [set:: s1 ++ s2] = [set:: s1] :|: [set:: s2].
Proof.
elim: s1 => /= [|a s1 IH].
   by rewrite set_nil set0U.
by rewrite !set_cons IH setUA.
Qed.

Lemma set_flatten (s : seq (seq T)) :
  [set:: flatten s] = \bigcup_(c <- s) [set:: c].
Proof.
elim: s => [|c s IH] /=.
  by rewrite big_nil.
by rewrite set_cat big_cons IH.
Qed.

Lemma bigcup2_set1 :
  \bigcup_(s in \bigcup_(i in P) G i) [set s] = \bigcup_(i in P) G i.
Proof.
apply/setP => i.
apply/bigcupP; case: ifPn.
  case/bigcupP => j jA ij.
  exists i => //. apply/bigcupP. exists j => //. by rewrite inE.
apply: contraNnot => -[] /= k /bigcupP[] x xA kx.
rewrite inE => /eqP ->.
by apply/bigcupP; exists x.
Qed.
End finset.

Section seq.
Lemma uniq_flatten (A : eqType) (s : seq (seq A)) :
  uniq (flatten s) -> {in s, forall c, uniq c}.
Proof.
elim: s => //= c s IH.
rewrite cat_uniq /= => /andP[] Hc /andP[NH Hs] d.
rewrite inE => /orP[/eqP -> // | ds].
by apply: IH.
Qed.

Variable (R : Type) (op : SemiGroup.com_law R).
Lemma big_seq_mkord A idx (s : seq A) (P : pred A) (F : A -> R) :
  let h := tnth (in_tuple s) in
  \big[op/idx]_(i <- s | P i) F i = \big[op/idx]_(i < size s | P (h i)) F (h i).
Proof.
move=> h.
rewrite /= -[in LHS](in_tupleE s) [in LHS](tuple_map_ord (in_tuple _)).
by rewrite big_map /= big_enum_cond.
Qed.
End seq.

Section behead.
Lemma beheadE A (x : A) (s : seq A) :
  ~~ nilp s -> head x s :: behead s = s.
Proof. by case: s => // a s. Qed.

Lemma take_behead A (s : seq A) m :
  m > 0 -> take m.-1 (behead s) = behead (take m s).
Proof. by move=> H; rewrite -!drop1 take_drop addn1 prednK. Qed.

Variables (T : finType) (f : T -> T) (k : T).
Lemma head_orbitE : head k (orbit f k) = k.
Proof. by rewrite /orbit; case: order. Qed.

Lemma orbit_beheadE : orbit f k = k :: behead (orbit f k).
Proof.
rewrite -[LHS](beheadE k); last by rewrite /nilp size_orbit -lt0n order_gt0.
by rewrite head_orbitE.
Qed.
End behead.

Section orbit.
Variables (n : nat) (p : 'I_n -> 'I_n) (Hp : injective p).

Lemma fcycle_eq p1 p2 x :
  x \in p1 -> x \in p2 -> fcycle p p1 -> fcycle p p2 -> p1 =i p2.
Proof.
move=> xp1 xp2 fp1 fp2 y.
rewrite -(fconnect_cycle fp1 xp1).
by rewrite -(fconnect_cycle fp2 xp2).
Qed.

Lemma fcycle_orbit_mem p1 x j :
  x \in p1 -> x \in orbit p j -> fcycle p p1 -> j \in p1.
Proof.
move=> xp1 xj /(fcycle_eq xp1 xj) ->; [exact: in_orbit | exact: cycle_orbit].
Qed.

Lemma eq_orbit_set i j :
  j \in orbit p i -> [set:: orbit p j] = [set:: orbit p i].
Proof.
move=> ji. apply/setP => x; rewrite !inE.
apply/esym/(fcycle_eq ji)/cycle_orbit/Hp/cycle_orbit/Hp/in_orbit.
Qed.

Lemma uniq_next_inj (A : eqType) (c : seq A) : uniq c -> injective (next c).
Proof. by move=> uc x y /(f_equal (prev c)); rewrite !prev_next. Qed.

Lemma iter_orbit i j : i \in orbit p j -> iter (index i (orbit p j)) p j = i.
Proof.
move=> ipj; rewrite /orbit -(nth_traject p (n:=order p j)).
  by rewrite nth_index.
by rewrite -{2}(size_traject p j (order p j)) index_mem.
Qed.

Lemma eq_orbit q : p =1 q -> orbit p =1 orbit q.
Proof.
move=> /= pq x.
have := cycle_orbit Hp x.
rewrite (eq_cycle (e':=frel q)); last by move=> /= y z; rewrite pq.
rewrite orbit_beheadE => /undup_cycle_cons <-.
by rewrite -orbit_beheadE undup_id.
Qed.

Lemma eq_order q : p =1 q -> order p =1 order q.
Proof. by move=> /eq_orbit Hx x; rewrite -!size_orbit Hx. Qed.
End orbit.

Section perm.
Variable n : nat.

(* A minimalist definition of permutations and transpositions *)
Definition is_perm (p : 'I_n -> 'I_n) := injective p.

Lemma is_perm_comp p1 p2 : is_perm p1 -> is_perm p2 -> is_perm (p1 \o p2).
Proof. by move=> inj1 inj2 x y /= /inj1 /inj2. Qed.

Definition tperm (i j : 'I_n) :=
  fun x => if x == i then j else if x == j then i else x.

Lemma tperm1 i j : tperm i j i = j.
Proof. by rewrite /tperm eqxx. Qed.

Lemma tperm2 i j : tperm i j j = i.
Proof. by rewrite /tperm eqxx; case: ifP => [/eqP|]. Qed.

Lemma tpermii i : tperm i i =1 id.
Proof. by rewrite /tperm => x; case: ifP => [/eqP // | ->]. Qed.

Lemma tpermK i j x : tperm i j (tperm i j x) = x.
Proof.
rewrite /tperm.
case/boolP: (x == i) => [/eqP -> | xi].
   case: ifP => [/eqP //|].
   by rewrite eqxx.
case/boolP: (x == j) => [/eqP -> | xj].
  by rewrite eqxx.
by rewrite (negbTE xi) (negbTE xj).
Qed.

Lemma is_tperm i j : is_perm (tperm i j).
Proof. by apply: bij_inj; exists (tperm i j) => x; rewrite tpermK. Qed.

Lemma tperm_id i j k : k != i -> k != j -> tperm i j k = k.
Proof. by rewrite /tperm => /negbTE -> /negbTE ->. Qed.

Lemma tpermC i j : tperm j i =1 tperm i j.
Proof.
rewrite /tperm /= => x.
case: ifP => /eqP xj; case: ifP => /eqP xi //; congruence.
Qed.

Lemma notin_tperm_id i j (s : seq 'I_n) :
  i \notin s -> j \notin s -> {in s, tperm i j =1 id}.
Proof.
move=> /= His Hjs x Hx.
apply: tperm_id.
- by apply/negP => /eqP xi; move: His; rewrite -xi Hx.
- by apply/negP => /eqP xj; move: Hjs; rewrite -xj Hx.
Qed.

Variable p : 'I_n -> 'I_n.
Hypothesis Hp : is_perm p.

(* Problem 1: decomposition of permutation *)

Definition decomposition :=
  foldl (fun d i => if i \in flatten d then d else orbit p i :: d)
        nil (ord_enum n).

Definition recompose (d : seq (seq 'I_n)) : 'I_n -> 'I_n :=
  \big[comp/id]_(c <- d) next c.

Definition decompose_cycle (c : seq 'I_n) :=
  match c with
  | nil => nil
  | a :: c' => [seq (a, b) | b <- c']
  end.

Definition shortest_seq := flatten (map decompose_cycle decomposition).

Definition recompose_perm (s : seq ('I_n * 'I_n)) :=
  foldr (fun ij g => g \o tperm ij.1 ij.2) id s.

Lemma is_recompose_perm s : is_perm (recompose_perm s).
Proof.
rewrite /recompose_perm.
elim: s => // -[i j] s IH /=.
  apply is_perm_comp; last by apply: is_tperm.
exact: IH.
Qed.

Lemma uniq_decomposition : uniq decomposition.
Proof.
rewrite /decomposition.
set d := [::].
have : uniq d by [].
elim: (ord_enum n) d => //= x s IH d Hu.
case: ifPn => Hi.
  by apply: IH.
apply: IH => //=.
rewrite Hu andbT /=.
apply: contra Hi => Hx.
apply/flattenP; exists (orbit p x) => //.
by rewrite in_orbit.
Qed.

Lemma uniq_flatten_decomposition : uniq (flatten decomposition).
Proof.
rewrite /decomposition.
set d := [::].
have : uniq (flatten d) by [].
have : forall c, c \in d -> fcycle p c by [].
elim: (ord_enum n) d => //= x s IH d Hfc Hu.
case: ifPn => Hi.
  by apply: IH.
apply: IH => //=.
  move=> c. rewrite inE => /orP[/eqP -> | /Hfc] //.
  by apply: cycle_orbit.
rewrite cat_uniq orbit_uniq Hu andbT /=.
apply/negP => /hasP[] /= y /flattenP[c'] c'd yc' yx.
elim: (negP Hi).
have xc' := fcycle_orbit_mem Hp yc' yx (Hfc _ c'd).
by apply/flattenP; exists c'.
Qed.

(* Alternative abstract decomposition, using finite sets *)

Definition cycles := [set [set:: orbit p i] | i in 'I_n].

Lemma trivIset_cycles : @trivIset 'I_n cycles.
Proof.
apply/trivIsetP => c1 c2.
case/imsetP => /= x Hx ->.
case/imsetP => /= y Hy -> c1c2.
apply/pred0Pn => -[z].
rewrite !inE => /andP[zx zy].
have /setseqP xy := fcycle_eq zx zy (cycle_orbit Hp x) (cycle_orbit Hp y).
by rewrite xy eqxx in c1c2.
Qed.

Lemma cover_cycles : cover cycles = [set: 'I_n].
Proof.
apply/setP => x.
rewrite !inE; apply/bigcupP.
exists [set y in orbit p x].
apply/imsetP.
  by exists x.
by rewrite inE in_orbit.
Qed.

Definition cycles_cover (s : seq (seq 'I_n)) : {set 'I_n} :=
  \bigcup_(l <- s) [set:: l].

Lemma decomposition_cycles :
  \bigcup_(c <- decomposition) [set [set:: c]] = cycles.
Proof.
rewrite /cycles /decomposition /=.
set d0 := [::].
transitivity ((\bigcup_(i <- ord_enum n) [set [set:: orbit p i]])
              :|: \bigcup_(c <- d0) [set [set:: c]]); last first.
  rewrite big_nil setU0 bigcup_seq imset_bigcup.
  by apply: congr_big => // x; rewrite mem_ord_enum inE.
have : uniq d0 by [].
have : forall c, c \in d0 -> fcycle p c by [].
elim: (ord_enum n) d0 => [|i r IH] d /= Hd Hu.
  by rewrite big_nil set0U.
case/boolP: (i \in flatten d) => Hid; last first.
  rewrite IH /=. by rewrite !big_cons setUC setUAC.
    move=> /= c; rewrite in_cons => /orP[/eqP -> | /Hd //].
    exact: cycle_orbit.
  rewrite Hu andbT.
  apply: contra Hid => od.
  apply/flattenP. exists (orbit p i) => //. exact: in_orbit.
rewrite IH // big_cons /=.
have Hincl : [set:: orbit p i] \in \bigcup_(c <- d) [set [set:: c]].
  case/flattenP: Hid => /= c cd ic.
  rewrite (bigD1_seq c) //=.
  move/Hd in cd.
  have -> : [set:: orbit p i] = [set:: c].
    apply/setP => /= x; rewrite !inE.
    exact/fcycle_eq/cd/cycle_orbit/Hp/ic/in_orbit.
  apply: setU11.
rewrite (setUC [set [set:: _]]) -setUA.
congr (_ :|: _).
apply/eqP; rewrite eqEsubset subsetU1 /=.
apply/subsetP => x /setUP[] //.
by rewrite inE => /eqP ->.
Qed.

(* Soundness of decomposition into cycles *)
Lemma recomposeE : recompose decomposition =1 p.
Proof.
move=> i.
rewrite /decomposition /=.
set d := nil.
set r := ord_enum n.
have : forall i, (i \in r) || (i \in flatten d).
  move=> j. apply/orP; left. exact: mem_ord_enum.
have : forall s, s \in d -> fcycle p s by [].
have : i \notin flatten d -> recompose d i = i.
  by rewrite /recompose big_nil.
have : i \in flatten d -> recompose d i = p i by [].
elim: r d => /= [|j r IH] d Hid Hid' Hd Hm /=.
  exact: Hid.
case/boolP: (j \in flatten d) => Hj.
  apply: IH => // k.
  move: (Hm k); rewrite inE -orbA => /orP[/eqP -> | -> //].
  by rewrite Hj orbT.
apply: IH.
- rewrite /= mem_cat => /orP[Hi|].
    rewrite /recompose big_cons /= [_ i]Hid'.
      by rewrite (nextE (cycle_orbit Hp j)).
    apply: contra Hj => /flattenP /= -[k kd ik].
    have Hj := fcycle_orbit_mem Hp ik Hi (Hd _ kd).
    by apply/flattenP; exists k.
  move => ifd.
  rewrite /recompose big_cons /= [_ i]Hid // next_nth ifF //.
  apply: contraNF Hj => pij.
  case/flattenP: ifd => /= c cd /(mem_fcycle (Hd _ cd)) ic.
  have Hj := fcycle_orbit_mem Hp ic pij (Hd _ cd).
  by apply/flattenP; exists c.
- rewrite /= mem_cat negb_or => /andP[Hij] /Hid' rdi.
  rewrite /recompose big_cons /= [X in next _ X]rdi.
  by rewrite next_nth (negbTE Hij).
- move=> s; rewrite inE => /orP[/eqP -> | /Hd //].
  exact: cycle_orbit.
- move=> k /=.
  move/orP: (Hm k) => [].
    rewrite inE => /orP[/eqP -> | -> //].
    by rewrite mem_cat in_orbit orbT.
  by rewrite mem_cat => ->; rewrite !orbT.
Qed.

Lemma next_at_out (c : seq 'I_n) x a b :
  x \notin (b::c) -> next_at x a b c = x.
Proof.
elim: c b => [|d c IH] b /=.
  by rewrite inE => /negbTE ->.
rewrite inE negb_or => /andP[xb xd].
by rewrite (negbTE xb) IH.
Qed.

Lemma next_out (c : seq 'I_n) x : x \notin c -> next c x = x.
Proof. by case: c => // a c; apply: next_at_out. Qed.

(* Soundness of decomposition of cycle into transpositions *)
Lemma recompose_cycleE c :
  uniq c ->
  recompose_perm (decompose_cycle c) =1 next c.
Proof.
case: c => [|a s] //.
elim: s => // [_ x | b s IH] /=.
  by case: ifP => // /eqP ->.
case/andP.
rewrite inE negb_or => /andP[ab Has] /andP[bs us] x /=.
case: ifPn => [/eqP -> | xa].
  rewrite tperm1 IH /=; last by rewrite Has us.
  by rewrite next_at_out // inE negb_or eq_sym ab bs.
transitivity (next (a::s) (tperm a b x)); first by rewrite IH //= Has.
rewrite /=.
have [-> | xb] := eqVneq x b.
  rewrite tperm2.
  by clear; case: s => [|d s] /=; rewrite !eqxx.
rewrite tperm_id //.
by clear -xa xb; case: s => [|d s] /=; rewrite (negbTE xa) (negbTE xb).
Qed.

Lemma recompose_perm_flatten s :
  recompose_perm (flatten s) = \big[compr/id]_(c <- s) recompose_perm c.
Proof.
rewrite /recompose_perm -(foldr_map _ compr) foldrE big_map (big_flatten compr).
apply: eq_bigr => c _.
rewrite -(big_map _ xpredT id) -foldrE.
by rewrite -[RHS](foldr_map _ compr).
Qed.

Section orbits.
Variables i j : 'I_n.
Hypothesis Hij : i != j.
Let orbj := orbit p j.
Let orbi' := behead (take (index i orbj) orbj).

Lemma i_notin_orbi' : i \notin orbi'.
Proof. by apply/negP => /mem_behead/index_ltn; rewrite ltnn. Qed.

Lemma  j_notin_orbi' : j \notin orbi'.
Proof.
move: (orbit_uniq p j).
rewrite orbit_beheadE /orbi' -/orbj => /andP[] /[swap] _.
apply: contra; clear.
case: index => [|m]. by rewrite take0.
by case: orbj => //= a l /mem_take.
Qed.

Hypothesis Hiorbj : i \in orbit p j.

Lemma ineqj_index_gt0 : index i (orbit p j) > 0.
Proof.
rewrite orbit_beheadE /=; case: ifP => //.
by rewrite eq_sym (negbTE Hij).
Qed.

Lemma p_last_take_index : p (tperm i j (last i orbi')) = i.
Proof.
have Hi : iter (index i orbj) p j = i by apply: iter_orbit.
rewrite (last_nth j) /orbi'.
rewrite size_behead size_takel; last by apply/ltnW; rewrite index_mem.
have : nth j orbj (index i orbj) = i by apply nth_index.
have Hin0 : index i orbj != 0 by rewrite -lt0n ineqj_index_gt0.
have [-> /= | Hin1 Hnth] := eqVneq (index i orbj) 1.
  rewrite tperm1 nth_traject //.
  have := iter_order Hp j.
  have := order_gt0 p j.
  case: order => // -[] //= _ pj.
  rewrite iter_fix // in Hi.
  move: Hij; by rewrite Hi eqxx.
have Hsz : index i orbj = (index i orbj).-2.+2.
  by case: (index i orbj) Hin0 Hin1 => // -[].
set nb := nth _ _ _.
have Hnb : nb \in orbi'.
  rewrite /nb -/orbi' Hsz /= mem_nth // /orbi'.
  move: Hiorbj; rewrite -index_mem -/orbj => Hiorbj'.
  rewrite size_behead size_takel; last by apply/ltnW.
  by rewrite Hsz.
rewrite (notin_tperm_id i_notin_orbi' j_notin_orbi' Hnb).
rewrite /nb {2}Hsz/= -drop1 nth_drop add1n nth_take; last by rewrite {2}Hsz.
rewrite nth_traject; last by rewrite -size_orbit -Hsz index_size.
by rewrite -iterS -Hsz Hi.
Qed.

Lemma cycle_split : fcycle (p \o tperm i j) (i :: orbi').
Proof.
rewrite /cycle /= rcons_path.
rewrite {2}/frel /= p_last_take_index eqxx andbT.
have := notin_tperm_id i_notin_orbi' j_notin_orbi'.
have : fpath p j orbi'.
  move: (cycle_orbit Hp j).
  rewrite (orbit_beheadE p j) /= rcons_path => /andP[].
  move/(take_path (index i orbj).-1).
  rewrite take_behead //.
  have : iter (index i orbj) p j = i by apply: iter_orbit.
  by rewrite ineqj_index_gt0.
have : head (p j) orbi' = p j.
  rewrite /orbi' /orbj.
  case: index => /=. by rewrite take0.
  case=> //. case: orbit => //= *. by rewrite take0.
  move=> k.
  rewrite /orbit.
  by case: order => //= -[].
case: orbi' => //= h orbi'' -> Hf Hh.
rewrite eqxx /= in Hf.
rewrite {1}/tperm eqxx eqxx /=.
rewrite (eq_in_path (P:=[in p j :: orbi'']) (e':=frel p)) //.
move=> x y /Hh Hx _ /=; by rewrite Hx.
Qed.

Lemma orbit_split : orbit (p \o tperm i j) i = i :: orbi'.
Proof.
rewrite -(undup_cycle_cons (p:=orbi')); last by apply: cycle_split.
apply: undup_id => /=.
apply/andP; split.
  apply/negP => io.
  move: (notin_tperm_id i_notin_orbi' j_notin_orbi' io).
  rewrite /tperm eqxx => /esym/eqP.
  by rewrite (negbTE Hij).
rewrite /orbi' -drop1.
by apply/drop_uniq/take_uniq/orbit_uniq.
Qed.

Let orbi := orbit p i.
Let orbj' := behead (take (index j orbi) orbi).
Hypothesis Hoij : [set:: orbit p i] == [set:: orbit p j].
Hypothesis Hjorbi : j \in orbi.

Lemma split_orbit x :
  (x \in i :: orbi') || (x \in j :: orbj') = (x \in orbi).
Proof.
case/boolP: (x \in i :: _) => /= [| xi].
  rewrite !inE => /orP[].
    rewrite /orbi orbit_beheadE inE => -> //.
  move/mem_behead/mem_take.
  move/eqP/setP/(_ x): Hoij.
  by rewrite !inE => <- ->.
case/boolP: (x \in j :: _) => /= [| xj].
  rewrite !inE => /orP[/eqP -> |].
    move/eqP/setP/(_ j): Hoij.
    rewrite !inE => ->.
    by rewrite in_orbit.
  by move/mem_behead/mem_take.
apply/esym/negP.
rewrite -(cat_take_drop (index j orbi) orbi).
rewrite mem_cat => /orP[].
  rewrite {2}/orbi orbit_beheadE.
  have Hsz : index j orbi = (index j orbi).-1.+1.
    by rewrite /orbi orbit_beheadE /= (negbTE Hij).
  rewrite Hsz take_cons Hsz take_behead // -Hsz -/orbj' inE => /orP[].
    move=> xi'. by rewrite inE xi' in xi.
  move=> xj'. by rewrite inE xj' orbT in xj.
have : orbj = rot (index j orbi) orbi.
  apply: orbitE => //. exact: cycle_orbit. exact: orbit_uniq.
rewrite rot_index => // Horbjd.
move: xi.
have Hsz : index i orbj = (index i orbj).-1.+1.
  by rewrite /orbj orbit_beheadE /= eq_sym (negbTE Hij).
rewrite /orbi' {2}Horbjd /= Hsz take_cons /= => xi.
rewrite drop_index // inE => /orP[xj' | xi'].
  by rewrite inE xj' in xj.
elim: (negP xi).
rewrite inE take_cat ifF.
  by rewrite mem_cat xi' orbT.
rewrite prednK; last by rewrite Hsz.
rewrite size_drop leq_subRL; last by rewrite index_mem.
rewrite addSn Horbjd -cat_cons index_cat.
rewrite ifF.
  rewrite /= size_drop -[(_ - _).+1]addn1 !addnA (addnC (index _ _)).
  rewrite -(addnA (_ - _)) addn1 subnK; last by rewrite index_mem.
  by rewrite -ltn_subRL subnn ltn0.
rewrite inE (negbTE Hij) -addn1 -drop_drop drop1 /=.
apply/negP => /mem_drop ib.
move: (orbit_uniq p i).
by rewrite orbit_beheadE /= ib.
Qed.
End orbits.

Section eq_orbit_in.
Variables i j k : 'I_n.
Hypothesis Hoij : [set:: orbit p i] == [set:: orbit p j].

Lemma in_orbit_mem : i \in orbit p j.
Proof.  move/eqP/setP/(_ i): Hoij; rewrite !inE => <-; exact: in_orbit. Qed.

Lemma eq_orbit_in :
  k \notin orbit p i -> orbit (p \o tperm i j) k = orbit p k.
Proof.
move=> Hk.
have Hok : {in orbit p k, forall x, tperm i j x = x}.
  move=> x Hx.
  rewrite -fconnect_orbit in Hx.
  rewrite /tperm.
  case: ifP => xi.
    rewrite (eqP xi) fconnect_sym // fconnect_orbit in Hx.
    by rewrite Hx in Hk.
  case: ifP => // xj.
  rewrite (eqP xj) fconnect_sym // fconnect_orbit in Hx.
  move/eqP/setP/(_ k): Hoij.
  rewrite !inE => Hoij'.
  rewrite -Hoij' in Hx.
  by rewrite Hx in Hk.
rewrite -(undup_cycle_cons (p:=behead (orbit p k))); last first.
  rewrite -orbit_beheadE.
  rewrite (eq_in_cycle (P:=[in orbit p k]) (e':=frel p)) //.
  - exact: cycle_orbit.
  - by move=> /= x y /Hok ->.
by rewrite -orbit_beheadE undup_id.
Qed.
End eq_orbit_in.

Section in_behead_orbit_id.
Variables i j : 'I_n.
Hypothesis Hoij : [set:: orbit p i] != [set:: orbit p j].

Lemma in_behead_orbit_id : {in behead (orbit p j), tperm i j =1 id}.
Proof.
apply/notin_tperm_id.
  by apply: contra Hoij => /mem_behead /eq_orbit_set ->.
move: (orbit_uniq p j).
by rewrite {1}orbit_beheadE /= => /andP[].
Qed.
End in_behead_orbit_id.

Section neq_orbit.
Variables i j : 'I_n.
Hypothesis Hoij : [set:: orbit p i] != [set:: orbit p j].

Let orbi' := behead (orbit p j) ++ j :: behead (orbit p i).

Lemma cycle_merge : fcycle (p \o tperm i j) (i :: orbi').
Proof.
rewrite /cycle rcons_path.
apply/andP; split.
  rewrite cat_path.
  have Hid := in_behead_orbit_id Hoij.
  move: (cycle_orbit Hp j).
  rewrite {1}orbit_beheadE /cycle rcons_path => /= /andP[pj pjb].
  apply/andP; split.
    case: (behead (orbit p j)) pj Hid => //= {}k l /andP[jk kl] Hid.
    apply/andP; split. by rewrite tperm1.
    rewrite (eq_in_path (P:=mem (k::l)) (e':=frel p)) // /frel /=.
      by move=> x y /Hid ->.
    by rewrite eqxx /=; apply/allP => x xl; apply/orP; right.
  apply/andP; split => /=.
    case: (behead (orbit p j)) Hid pjb => /= [_|{}k l -> //].
      by rewrite tperm1.
    by rewrite mem_last.
  move: (cycle_orbit Hp i).
  rewrite {1}orbit_beheadE /cycle rcons_path => /= /andP[pi _].
  move: Hoij; rewrite eq_sym => Hoji.
  have := in_behead_orbit_id Hoji.
  case: (behead (orbit p i)) pi => //= {}k l /andP[ik kl] Hid'.
  apply/andP; split. by rewrite tperm2.
  rewrite (eq_in_path (P:=mem (k::l)) (e':=frel p)) // /frel /=.
    move=> x y /= /Hid'. by rewrite tpermC => ->.
  by rewrite eqxx /=; apply/allP => x xl; apply/orP; right.
rewrite /orbi' /= last_cat /=.
move: (cycle_orbit Hp i).
rewrite {1}orbit_beheadE /cycle rcons_path => /= /andP[_ pbi].
move: Hoij; rewrite eq_sym => Hoji.
have := in_behead_orbit_id Hoji.
case: (behead (orbit p i)) pbi => /= [|{}k l] pi.
  by rewrite tperm2.
move/(_ (last k l)) => <-. by rewrite tpermC tpermK.
by rewrite mem_last.
Qed.

Lemma orbit_merge : orbit (p \o tperm i j) i = i :: orbi'.
Proof.
rewrite -(undup_cycle_cons (p:=orbi')); last by apply: cycle_merge.
apply: undup_id.
rewrite /orbi' -cat_cons -(cat1s i) -(cat1s j).
rewrite uniq_catCA -!catA uniq_catCA.
rewrite (catA [:: j]) uniq_catCA !cat1s -!orbit_beheadE.
rewrite cat_uniq !orbit_uniq //= andbT.
apply/hasP => /= -[x] /eq_orbit_set xi /eq_orbit_set xj.
by move: Hoij; rewrite -xi // -xj // eqxx.
Qed.
End neq_orbit.

Lemma decomposition_rev :
  \big[compr/id]_(c <- decomposition) next c =1
  \big[comp/id]_(c <- decomposition) next c.
Proof.
rewrite /decomposition /=.
set d := [::].
have : {in d, forall c, fcycle p c} by [].
have : forall x, x \notin flatten d -> (\big[compr/id]_(c <- d) next c) x = x.
  by rewrite big_nil.
have :
  {in flatten d, forall x, (\big[compr/id]_(c <- d) next c) x \in flatten d}.
  by [].
have : \big[compr/id]_(c <- d) next c =1 \big[comp/id]_(c <- d) next c.
  by rewrite !big_nil.
elim: (ord_enum n) d => //= i l IH d Hd Hfd Hdisj Hc.
case: ifPn => Hi. by apply: IH.
have Hi' : {in orbit p i, forall x, x \notin flatten d}.
  move=> j Hj.
  apply: contra Hi => /flattenP /= -[c cd jc].
  have Hi := fcycle_orbit_mem Hp jc Hj (Hc _ cd).
  by apply/flattenP; exists c.
apply IH => //.
- rewrite !big_cons {1}/compr.
  move=> j /=.
  rewrite -Hd.
  case/boolP: (j \in orbit p i) => Hj.
    rewrite !Hdisj //.
    + exact: Hi'.
    + have Hj' := mem_orbit Hj.
      by rewrite (nextE (cycle_orbit Hp i)) // Hi'.
  rewrite next_out //.
  case/boolP: (j \in flatten d) => Hjd; last first.
    by rewrite Hdisj // next_out.
  rewrite next_out //.
  apply: contraTN (Hfd _ Hjd) => Hj'.
  exact: Hi'.
- rewrite big_cons => /= j.
  rewrite mem_cat {1}/compr /= => /orP[] Hj.
    rewrite mem_cat; apply/orP; left.
    rewrite (nextE (cycle_orbit Hp i)) //.
    rewrite Hdisj.
      exact: mem_orbit.
    move/mem_orbit in Hj.
    exact: Hi'.
  rewrite mem_cat; apply/orP; right.
  rewrite next_out; last first.
    apply: contraTN Hj => Hj'.
    exact: Hi'.
  exact: Hfd.
- move=> x.
  rewrite /= mem_cat negb_or => /andP [xi xd].
  by rewrite big_cons {1}/compr /= Hdisj // next_out.
- move=> x.
  rewrite inE => /orP[/eqP -> | xd].
    exact: cycle_orbit.
  exact: Hc.
Qed.

(* Soundness of decomposition intro transpositions *)
Lemma recompose_permE : recompose_perm shortest_seq =1 p.
Proof.  
move=> x.
rewrite recompose_perm_flatten big_map.
rewrite big_seq.
under eq_bigr => /= c Hc.
  have/recompose_cycleE := uniq_flatten (uniq_flatten_decomposition) Hc.
  move/boolp.funext => ->.
  over.
by rewrite -big_seq decomposition_rev -/(recompose decomposition) recomposeE.
Qed.
End perm.

(* Main lemma: composing a transposition decreases the number of cycles
   by at most 1 *)
Lemma add_transposition n p (i j : 'I_n) :
  is_perm p -> i != j ->
  #|cycles (p \o tperm i j)| = #|cycles p| + 1 \/
  #|cycles (p \o tperm i j)| = #|cycles p| - 1.
Proof.
move=> Hp Hij.
have Hpij : is_perm (p \o tperm i j) by apply/is_perm_comp/is_tperm.
case/boolP: ([set:: orbit p i] == [set:: orbit p j]) => Hoij.
- left.
  set orbj := orbit p j.
  set orbi' := behead (take (index i orbj) orbj).
            (* traject p (p j) (index i orbj).-1.*)
  rewrite /= in orbj orbi'.
  have Hiorbj := eq_orbit_in Hp Hoij.
  (*have Hlast : p (tperm i j (last i orbi')) = i by apply: p_last_take_index.*)
  have Horb : orbit (p \o tperm i j) i = i :: orbi'.
    apply: orbit_split => //. exact: in_orbit_mem.
  have Hother := eq_orbit_in Hp Hoij.
  pose orbi := orbit p i.
  pose orbj' := behead (take (index j orbi) orbi).
  have Horbj : orbit (p \o tperm i j) j = j :: orbj'.
    rewrite (eq_orbit Hpij (q:=p \o tperm j i)) ; last first.
      by move=> x /=; rewrite tpermC.
    rewrite eq_sym in Hij.
    apply: orbit_split => //. apply: in_orbit_mem. by rewrite eq_sym.
  have Horbij : [set:: orbit (p \o tperm i j) i] !=
                [set:: orbit (p \o tperm i j) j].
    apply/eqP => /esym/setP/(_ i).
    by rewrite Horb Horbj !inE eqxx (negbTE Hij) (negbTE (j_notin_orbi' _ _ _)).
  have Hjorbi : j \in orbi by apply: in_orbit_mem; rewrite eq_sym.
  rewrite /cycles !imset_bigcup.
  rewrite (bigID [in orbit (p \o tperm i j) i]) /=.
  rewrite (bigcup_same (i:=i)); first last.
  - by rewrite topredE in_orbit.
  - by move=> k /eq_orbit_set ->.
  rewrite (bigID [in orbit (p \o tperm i j) j]) /=.
  rewrite (bigcup_same (i:=j)); first last.
  - by rewrite in_orbit andbT; apply: contra Horbij => /eq_orbit_set ->.
  - by move=> k /andP[_] /eq_orbit_set ->.
  rewrite (_ : \bigcup_(k < n | _) _ =
               \bigcup_(k < n | k \notin orbi) [set [set:: orbit p k]]).
  rewrite [in RHS](bigID [in orbi]) /=.
  rewrite [in RHS](bigcup_same (i:=i)); first last.
  - by rewrite topredE in_orbit.
  - by move=> k /eq_orbit_set ->.
  rewrite setUA !cardsU !cards1 !disjoint_setI0.
  by rewrite !cards0 !subn0 !addn1 add1n add2n.
  - apply/pred0Pn => -[c] /= /andP[].
    rewrite inE => /eqP -> /bigcupP[] /= x Hx.
    rewrite inE => /eqP/setP /(_ x).
    by rewrite !inE (negbTE Hx) in_orbit.
  - apply/pred0Pn => -[c] /= /andP[].
    rewrite !inE Horb Horbj => Hc.
    have /= {}Hc : {in c, forall x, x \in orbi}.
      move=> x. rewrite -(split_orbit Hp Hij) //.
      case/orP: Hc => /eqP => ->; rewrite !inE => -> //; by rewrite orbT.
    case/bigcupP => x Hx; rewrite inE => /eqP cx.
    by rewrite Hc // cx inE in_orbit in Hx.
  - apply/pred0Pn => -[c] /= /andP[].
    rewrite !inE => /eqP ->.
    by rewrite (negbTE Horbij).
  - apply congr_big => //=.
    + move=> x; by rewrite -negb_or Horb Horbj split_orbit.
    + move=> k.
      by rewrite -negb_or Horb Horbj split_orbit // => /Hother ->.
right.
set orbi' := behead (orbit p j) ++ j :: behead (orbit p i).
have Horbi' : orbit (p \o tperm i j) i = i :: orbi' by apply: orbit_merge.
rewrite /cycles !imset_bigcup.
rewrite (bigID [in orbit (p \o tperm i j) i]) /=.
rewrite [in RHS](bigID [in orbit p i]) /=.
rewrite [\bigcup_(k < n | k \notin orbit p i) _](bigID [in orbit p j]) /=.
rewrite (bigcup_same (i:=i)); first last.
- exact: in_orbit.
- by move=> /= k /eq_orbit_set ->.
rewrite [in RHS](bigcup_same (i:=i)); first last.
- exact: in_orbit.
- by move=> /= k /eq_orbit_set ->.
rewrite [in RHS](bigcup_same (i:=j)); first last.
- case/boolP: (j \in _).
    by move/eq_orbit_set => // Hj; rewrite Hj // eqxx in Hoij.
  by rewrite in_orbit.
- by move=> /= k /andP[_] /eq_orbit_set ->.
rewrite setUA !cardsU !cards1.
rewrite !disjoint_setI0.
rewrite !cards0 !subn0 !addn1 add1n add2n subn1 /=.
congr (#|_|.+1).
f_equal.
apply: congr_big => //=.
- move=> k.
  rewrite -negb_or; congr negb.
  rewrite Horbi' orbit_beheadE (orbit_beheadE p j).
  rewrite /orbi' !inE mem_cat !inE -orbA.
  rewrite (orbC (k \in _)).
  by rewrite [in RHS](orbC (k \in _)) -!orbA (orbC (k \in _)).
- move=> k Hk.
  have -> // : orbit (p \o tperm i j) k = orbit p k.
  rewrite orbit_beheadE.
  rewrite -(undup_cycle_cons (p:=behead (orbit p k))).
    by rewrite -orbit_beheadE undup_id ?orbit_uniq // -orbit_beheadE.
  rewrite (eq_in_cycle (P:=mem (k::behead (orbit p k))) (e':=frel p)) //;
    rewrite -orbit_beheadE /=.
  * exact: cycle_orbit.
  * move => x y /= /= /eq_orbit_set Hx _.
    move/(_ Hp)/esym/eqP/in_orbit_mem in Hx.
    rewrite Horbi' /orbi' in Hk.
    rewrite tperm_id //.
    + apply/negP => /eqP xi.
      move: Hx; rewrite xi orbit_beheadE inE => /orP[] Hx; elim: (negP Hk).
        by rewrite inE Hx.
      by rewrite inE mem_cat inE Hx !orbT.
    + apply/negP => /eqP xj.
      move: Hx; rewrite xj orbit_beheadE inE => /orP[] Hx; elim: (negP Hk).
        by rewrite inE mem_cat inE Hx !orbT.
      by rewrite inE mem_cat Hx orbT.
  * by apply/allP => x Hx.
- apply/pred0Pn => /= -[c].
  rewrite !inE => /andP[] /orP[] /eqP -> /bigcupP [{}c] /andP[ci cj];
    rewrite inE eq_sym => /in_orbit_mem.
    by rewrite (negbTE ci).
  by rewrite (negbTE cj).
- apply/pred0Pn => /= -[c]; rewrite !inE => /andP[] /eqP ->.
  by rewrite (negbTE Hoij).
- apply/pred0Pn => /= -[c]; rewrite !inE => /andP[] /eqP ->.
  move/bigcupP => -[{}c Hc].
  rewrite inE eq_sym => /in_orbit_mem Hc'.
  by rewrite Hc' in Hc.
Qed.

Lemma eq_cycles n (p q : 'I_n -> 'I_n) :
  is_perm p -> p =1 q -> cycles p = cycles q.
Proof. by move=> Hp pq; apply: eq_imset => x; rewrite (eq_orbit Hp pq x). Qed.

Lemma ncycles_id n : #|cycles (id : 'I_n -> 'I_n)| = n.
Proof.
rewrite /cycles card_imset. by rewrite card_ord.
move=> /= x y. rewrite !orbit_id => /setP /(_ y).
by rewrite !inE eqxx eq_sym => /eqP.
Qed.

Lemma leq_ncycles n (p : 'I_n -> 'I_n) : #|cycles p| <= n.
Proof. by rewrite /cycles -[X in _ <= X]card_ord leq_imset_card. Qed.

Lemma ncycles_gt0 n (p : 'I_n -> 'I_n) i : i \in 'I_n -> #|cycles p| > 0.
Proof.
move=> Hi. rewrite /cycles imset_bigcup (bigD1 i) //=.
rewrite card_gt0. apply/eqP => /setP/(_ [set:: orbit p i]).
by rewrite !inE eqxx.
Qed.

(* Minimal size *)
Lemma ncycles_tperms n (s : seq ('I_n * 'I_n)) :
  size s >=
    n - #|cycles (recompose_perm s)|.
Proof.
elim: s => [|[i j] s IH] /=.
  by rewrite ncycles_id subnn.
case/boolP: (i == j) => [/eqP <- |].
  rewrite (eq_cycles (q:=recompose_perm s));
      last by move=> /= x; rewrite tpermii.
    by apply/ltnW; rewrite ltnS IH.
  apply/is_perm_comp/is_tperm/is_recompose_perm.
move=> ij; case: (add_transposition (@is_recompose_perm _ s) ij) => ->.
  rewrite addn1 subnS (leq_trans (leq_pred _)) //.
  by apply/ltnW; rewrite ltnS // IH.
rewrite subnA; last by rewrite leq_ncycles.
  by rewrite addn1 ltnS IH.
by rewrite (ncycles_gt0 _ (i:=i)).
Qed.

(* Problem 2 : minimality of permutation decomposition *)

Theorem decomposition_minimal n (s : seq ('I_n * 'I_n)) :
  size s >= size (shortest_seq (recompose_perm s)).
Proof.
rewrite /=.
have := @is_recompose_perm _ s.
set p := recompose_perm s => Hp.
apply: (leq_trans _ (ncycles_tperms s)).
rewrite size_flatten /shape -map_comp.
rewrite (eq_map (g:=fun x => size x - 1)); last first.
  case => // a c /=.
  by rewrite size_map subn1.
rewrite sumnE big_map big_seq sumnB /=; last first.
  move=> c Hc.
  have : [set:: c] \in cycles p.
    rewrite -decomposition_cycles // big_seq_mkord /=.
    rewrite -index_mem in Hc.
    apply/bigcupP; exists (Ordinal Hc) => //.
    by rewrite (tnth_nth c) /= nth_index ?inE -?index_mem.
  case/imsetP => x d /setP/(_ x).
  rewrite !inE in_orbit -index_mem => Hsc.
  by apply: (leq_trans _ Hsc).
rewrite -!big_seq -(big_map size xpredT id) -sumnE.
rewrite big_const_seq count_predT iter_addn mul1n addn0.
rewrite -size_flatten.
have/card_uniqP <- := uniq_flatten_decomposition Hp.
rewrite -cardsE.
rewrite (eq_card (B:=\bigcup_(c in cycles p) c)); last first.
  apply/setP.
  rewrite set_flatten.
  rewrite -(big_map (fun x => [set:: x]) xpredT id).
  rewrite bigcup_seq.
  apply: eq_bigl => /= x.
  rewrite -decomposition_cycles //.
  rewrite -(big_map (fun x => [set:: x]) xpredT) bigcup_seq.
  by rewrite -imset_bigcup mem_imset.
rewrite -/(cover (cycles p)) cover_cycles cardsE card_ord leq_sub2l //.
rewrite -decomposition_cycles //.
elim: (decomposition p) => [|c d IH] /=.
  by rewrite big_nil cards0.
by rewrite big_cons cardsU1 -add1n leq_add // leq_b1.
Qed.

(* Problem 3 : sorting a list *)
Section minsort.
Section defs.
Variables (n : nat) (s : n.-tuple nat).

Lemma index_sorted_ltn x :
  index (tnth (sort_tuple leq s) x) s < n.
Proof.
by rewrite -[X in _ < X](size_tuple s) index_mem -(mem_sort leq s) mem_tnth.
Qed.

Definition perm_of_sort : 'I_n -> 'I_n :=
  fun x => Ordinal (index_sorted_ltn x).

Definition apply_perm (p : 'I_n -> 'I_n) := [tuple tnth s (p i) | i < n].

Definition exchange (i j : 'I_n) :=
  [tuple if k == i then tnth s j else if k == j then tnth s i else tnth s k
  | k < n].
End defs.

Definition apply_seq n (ts : seq ('I_n * 'I_n)) s :=
  foldr (fun (p : 'I_n * 'I_n) s => exchange s p.1 p.2) s ts.

Lemma exchanges_applyE n s (ts : seq ('I_n * 'I_n)) :
  apply_perm s (recompose_perm ts) = apply_seq ts s.
Proof.
rewrite /recompose_perm.
elim: ts s => /= [|[i j] ts IH] s.
  by apply/eq_from_tnth => i; rewrite tnth_mktuple.
rewrite -IH /apply_perm.
apply/eq_from_tnth => k; rewrite !tnth_mktuple /= {2}/tperm.
by case: ifP => //; case: ifP.
Qed.

Lemma tnth_perm_of_sort n (s : n.-tuple nat) i :
  tnth s (perm_of_sort s i) = tnth (sort_tuple leq s) i.
Proof.
case: n s i => /= [| n] s i; first by case: i.
rewrite (tnth_nth (tnth s ord0)) /perm_of_sort /=.
by rewrite nth_index // -(mem_sort leq s) mem_tnth.
Qed.

Lemma sorted_apply_perm n (s : n.-tuple nat) :
  apply_perm s (perm_of_sort s) = sort_tuple leq s.
Proof.
by apply: eq_from_tnth => i; rewrite !tnth_mktuple tnth_perm_of_sort.
Qed.

Variables (n : nat) (s : n.-tuple nat).
Hypothesis Hu : uniq s.

Lemma is_perm_of_sort : is_perm (perm_of_sort s).
Proof.
move: Hu; rewrite -(sort_uniq leq s) => /tuple_uniqP => Hinj.
move=> i j /(f_equal (tnth s)).
by rewrite !tnth_perm_of_sort => /Hinj.
Qed.

Lemma recompose_sorted :
  apply_seq (shortest_seq (perm_of_sort s)) s = sort_tuple leq s.
Proof.
rewrite -exchanges_applyE.
apply: eq_from_tnth => i.
rewrite tnth_mktuple recompose_permE ?tnth_perm_of_sort //.
exact: is_perm_of_sort.
Qed.

Lemma perm_eq_exchange (s1 : n.-tuple nat) i j :
  perm_eq s1 (exchange s1 i j).
Proof.
apply/permP => p.
rewrite -!sumn_count !sumnE 3!big_map {1}(tuple_map_ord s1) big_map.
rewrite val_ord_tuple !big_enum /=.
rewrite (reindex (tperm i j)) /=; last exact/onW_bij/injF_bij/is_tperm.
apply: eq_bigr => k _.
rewrite /tperm.
by case: ifP => //; case: ifP.
Qed.

Lemma perm_eq_apply_seq ts (s1 : n.-tuple nat) :
  perm_eq s1 (apply_seq ts s1).
Proof.
elim: ts => // -[i j] ts IH.
rewrite /apply_seq [exchange]lock /= -lock.
exact: (perm_trans IH (perm_eq_exchange _ i j)).
Qed.

Lemma apply_perm_inj : injective (apply_perm s).
Proof.
move=> p1 p2 H.
apply: boolp.funext => i.
move/(f_equal (@tnth _ _ ^~ i)): H.
rewrite !tnth_mktuple.
by move/tuple_uniqP: Hu => Hinj /Hinj.
Qed.

(* Optimal answer to problem 3 *)
Theorem shortest_seq_minimal ts :
  sorted leq (apply_seq ts s) ->
  size ts >= size (shortest_seq (perm_of_sort s)).
Proof.
move=> H.
have Happ : apply_seq ts s = sort_tuple leq s.
  apply/val_inj => /=.
  apply: (sorted_eq leq_trans anti_leq) => //.
  - exact/sort_sorted/Order.le_total.
  - by rewrite perm_sym (perm_trans _ (perm_eq_apply_seq ts s)) // perm_sort.
have <- : recompose_perm ts = perm_of_sort s.
  have := exchanges_applyE s ts.
  by rewrite Happ -sorted_apply_perm => /apply_perm_inj.
exact: decomposition_minimal.
Qed.
End minsort.

Require Import Coq.Program.Equality.

Lemma idPT : @idP true = ReflectT true is_true_true.
Proof.
move: idP => x.
dependent destruction x.
congr ReflectT.
exact: bool_irrelevance.
Qed.

Definition succO {n} := lift (@ord0 n).
Definition one {n} := @succO n.+1 ord0.

Lemma ord_enumE n : enum 'I_n = ord_enum n.
Proof. by apply/(inj_map val_inj); rewrite val_enum_ord val_ord_enum. Qed.

Lemma decompose3 :
  decomposition (tperm ord0 (one : 'I_3)) =
    [:: [:: succO (succO ord0)]; [:: ord0; succO ord0]].
Proof.
cbv.
rewrite -enumT ord_enumE /=.
rewrite cardT /= ord_enumE /=.
rewrite card.unlock /= /enum_mem /= -enumT ord_enumE /=.
cbv.
rewrite !idPT /=.
do !congr cons; by apply/val_inj.
Qed.

Lemma decompose_tperm3 :
  shortest_seq (tperm ord0 (one : 'I_3)) = [:: (ord0, succO ord0)].
Proof. by rewrite /shortest_seq decompose3 /=. Qed.

Require Import Extraction.
Extraction "decomposition.ml" decomposition.
