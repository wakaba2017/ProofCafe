From mathcomp Require Import all_ssreflect.

Section Nagoya2013.

  Definition Sk k n := \sum_(1 <= i < n.+1) i ^ k.
  Variable m : nat.
  Hypothesis Hm : m > 1.
  Definition Tm n := \sum_(1 <= k < m) 'C(m, k) * Sk k n. (* binomial.v 参照*)

  Check big_nat1
        : forall (R : Type) (idx : R) (op : Monoid.law idx) (n : nat) (F : nat -> R),
            \big[op/idx]_(n <= i < n.+1) F i = F n.

  Lemma Sk1 k :
    Sk k 1 = 1.
  Proof.
    by rewrite /Sk big_nat1 exp1n.
    (*
      Sk k 1 = 1.
      ↓
      ↓rewrite /Sk.
      ↓
      \sum_(1 <= i < 2) i ^ k = 1
      ↓
      ↓rewrite big_nat1.
      ↓
      1 ^ k = 1
      ↓
      ↓rewrite exp1n.
      ↓
      1 = 1
    *)
  Qed.

  Lemma Tm1 :
    Tm 1 = 2 ^ m - 2.
  Proof.
    rewrite /Tm.
    rewrite [in 2 ^ m](_ : 2 = 1 + 1) //.
    rewrite Pascal. (* 二項公式*)
    transitivity ((\sum_(0 <= k < m.+1) 'C(m, k)) - 2).
      symmetry.
      rewrite (@big_cat_nat _ _ _ m) //=.
      rewrite (@big_cat_nat _ _ _ 1) //=; last by apply ltnW.
      rewrite addnAC !big_nat1 bin0 binn addKn.
      apply eq_bigr => i H.
      by rewrite Sk1 muln1.
    rewrite big_mkord.
    congr (_ - _).
    apply eq_bigr => i _.
    by rewrite !exp1n !muln1.
  Qed.

  Search (_ ^ _) "exp". (* 自然数の指数関数expn に関する様々な補題*)

  Lemma Tm2 :
    Tm 2 = 3 ^ m - 3.
  Proof.
    rewrite /Tm.
    have ->: 3 ^ m - 3 = 2 ^ m - 2 + (3 ^ m - 1 - 2 ^ m).
      (* 追加ここから *)
      rewrite addnC addnBA.
      - rewrite subnK.
        + by rewrite -subnDA.
        + (*
            2 ^ m <= 3 ^ m - 1
            2 ^ m <= (2 + 1) ^ m - 1
            2 ^ m <= \sum_(i < m.+1) 'C(m, i) * (2 ^ (m - i) * 1 ^ i) - 1
            2 ^ m <= 'C(m, 0) * (2 ^ (m - 0) * 1 ^ 0) +
                     \sum_(1 <= i < m.+1) 'C(m, i) * (2 ^ (m - i) * 1 ^ i) - 1
            2 ^ m <= 1 * (2 ^ m * 1) +
                     \sum_(1 <= i < m.+1) 'C(m, i) * (2 ^ (m - i) * 1 ^ i) - 1
            2 ^ m <= 2 ^ m +
                     \sum_(1 <= i < m.+1) 'C(m, i) * (2 ^ (m - i) * 1 ^ i) - 1
                0 <= \sum_(1 <= i < m.+1) 'C(m, i) * (2 ^ (m - i) * 1 ^ i) - 1
                0 <= \sum_(1 <= i < m) 'C(m, i) * (2 ^ (m - i) * 1 ^ i) +
                    'C(m, m) * (2 ^ (m - m) * 1 ^ m) - 1
                0 <= \sum_(1 <= i < m) 'C(m, i) * (2 ^ (m - i) * 1 ^ i) +
                     1 * (2 ^ 0 * 1) - 1
                0 <= \sum_(1 <= i < m) 'C(m, i) * (2 ^ (m - i) * 1 ^ i) + 1 - 1
                0 <= \sum_(1 <= i < m) 'C(m, i) * (2 ^ (m - i) * 1 ^ i)
          *)
          rewrite [in 3 ^ m](_ : 3 = 2 + 1); last done.
          rewrite Pascal.
          rewrite -(@big_mkord _ 0 addn m.+1 (fun n => true) (fun i => 'C(m, i) * (2 ^ (m - i) * 1 ^ i))).
          rewrite big_nat_recl.
          rewrite bin0 subn0 expn0 mul1n muln1.
          rewrite -{1}[2 ^ m]addn0.
          rewrite -{3}[m]prednK; last by apply: (@ltn_trans 1 0 m).
          rewrite big_nat_recr /=.
          + rewrite prednK; last by apply: (@ltn_trans 1 0 m).
            rewrite binn exp1n subnn expn0 !mul1n addnA addn1 subn1 PeanoNat.Nat.pred_succ.
            by rewrite leq_add2l.
          + rewrite leq_eqVlt; apply/orP; right.
            by rewrite -(@ltn_add2r 1) add0n addn1 prednK; last by apply: (@ltn_trans 1 0 m).
          rewrite leq_eqVlt; apply/orP; right.
          by apply: (@ltn_trans 1 0 m).
      - rewrite -{1}(exp1n m) ltn_exp2r; first done.
        by apply: (@ltn_trans 1 0 m).
      (* 追加ここまで *)
    rewrite -Tm1.
    rewrite [in 3 ^ m](_ : 3 = 1 + 2) //.
    rewrite Pascal.
    transitivity (Tm 1 + (\sum_(1 <= k < m) 'C(m, k) * 2 ^ k)).
      rewrite -big_split /=.
      apply eq_bigr => i _.
      rewrite /Sk !big_cons !big_nil.
      by rewrite !addn0 -mulnDr.
    congr (_ + _).
    transitivity ((\sum_(0 <= k < m.+1) 'C(m, k) * 2 ^ k) - 1 - 2 ^ m).
    (* 追加ここから *)
      rewrite [in RHS]big_nat_recr /=. 
      - rewrite binn mul1n.
        rewrite [in RHS]big_ltn; last by apply: (@ltn_trans 1 0 m).
        rewrite bin0 expn0 muln1.
        rewrite -addnA addnC -subnDA [1 + 2 ^ m]addnC -addnA -addnBA; last done.
        by rewrite subnn addn0.
      - apply: ltnW.
        by apply: (@ltn_trans 1 0 m).
    rewrite big_mkord.
    have -> : \sum_(i < m.+1) 'C(m, i) * 2 ^ i =
              \sum_(i < m.+1) 'C(m, i) * (1 ^ (m - i) * 2 ^ i).
      rewrite -(@big_mkord _ 0 addn m.+1 (fun n => true) (fun i => 'C(m, i) * 2 ^ i)).
      rewrite -(@big_mkord _ 0 addn m.+1 (fun n => true) (fun i => 'C(m, i) * (1 ^ (m - i) * 2 ^ i))).
      apply: (@eq_big_nat _ 0 addn 0 m.+1 (fun i => 'C(m, i) * 2 ^ i) (fun i => 'C(m, i) * (1 ^ (m - i) * 2 ^ i))) => i.
      by rewrite exp1n mul1n.
    by [].
    (* 追加ここまで *)
  Qed.

  Theorem Tmn n :
    Tm n.+1 = n.+2 ^ m - n.+2.
  Proof.
    elim: n => [|n IHn] /=.
      by apply Tm1.
    have Hm': m > 0 by apply ltnW.
    have ->: n.+3 ^ m - n.+3 = n.+2 ^ m - n.+2 + (n.+3 ^ m - 1 - n.+2 ^ m).
    (* 追加ここから *)
      rewrite addnC addnBA.
      - rewrite subnK.
        + by rewrite -subnDA addnC addn1.
        + rewrite -[n.+3]addn1 Pascal.
          rewrite -(@big_mkord _ 0 addn m.+1 (fun n => true) (fun i => 'C(m, i) * (n.+2 ^ (m - i) * 1 ^ i))).
          rewrite big_nat_recl; last by apply: ltnW.
          rewrite bin0 subn0 expn0 mul1n muln1 -{1}[n.+2 ^ m]addn0.
          rewrite -{3}[m]prednK; last by apply: (@ltn_trans 1 0 m).
          rewrite big_nat_recr /=.
          * rewrite prednK; last by apply: (@ltn_trans 1 0 m).
            rewrite binn exp1n subnn expn0 !mul1n addnA addn1 subn1 PeanoNat.Nat.pred_succ.
            by rewrite leq_add2l.
          * rewrite leq_eqVlt; apply/orP; right.
            by rewrite -(@ltn_add2r 1) add0n addn1 prednK; last by apply: (@ltn_trans 1 0 m).
      - rewrite -[n.+2]addn1 Pascal.
        rewrite -(@big_mkord _ 0 addn m.+1 (fun n => true) (fun i => 'C(m, i) * (n.+1 ^ (m - i) * 1 ^ i))).
        rewrite big_nat_recr /=.
        + rewrite binn exp1n subnn expn0 !mul1n.
          rewrite -{1}[m]prednK; last by apply: (@ltn_trans 1 0 m).
          rewrite big_nat_recr /=.
          * rewrite -{4}[m]prednK; last done.
            rewrite binSn prednK; last done.
            rewrite -subn1 subKn; last done.
            rewrite expn1 exp1n muln1.
            rewrite -{4}[m]prednK; last done.
            rewrite -[m.-1.+1]addn1 mulnDl mul1n -addnA -[_ + n.+1 + 1]addnA addnA.
            rewrite -{1}[n.+1 + 1]add0n (@leq_add2r (n.+1 + 1)).
            by [].
          * rewrite leq_eqVlt; apply/orP; right.
            by rewrite -(@ltn_add2r 1) add0n addn1 prednK; last by apply: (@ltn_trans 1 0 m).
        + by apply: ltnW.
    (*
      この時点でゴールは次の形になっている。
      m : nat
      Hm : 1 < m
      n : nat
      IHn : Tm n.+1 = n.+2 ^ m - n.+2
      Hm' : 0 < m
      ______________________________________(1/1)
      Tm n.+2 = n.+2 ^ m - n.+2 + (n.+3 ^ m - 1 - n.+2 ^ m)
    *)
    rewrite -IHn /Tm /Sk.
    (*
        \sum_(1 <= k < m) 'C(m, k) * (\sum_(1 <= i < n.+3) i ^ k)
      = \sum_(1 <= k < m) 'C(m, k) * (\sum_(1 <= i < n.+2) i ^ k + n.+2 ^ k)
      = \sum_(1 <= k < m) 'C(m, k) * \sum_(1 <= i < n.+2) i ^ k +
        \sum_(1 <= k < m) 'C(m, k) * n.+2 ^ k

        \sum_(1 <= k < m) 'C(m, k) * n.+2 ^ k
      = 'C(m, 1)    * n.+2 ^ 1 +
        ... +
        'C(m, m.-1) * n.+2 ^ m.-1

        n.+3 ^ m - 1 - n.+2 ^ m
      = n.+3 ^ m - 1 - n.+2 ^ m
      = (n.+2 + 1) ^ m - 1 - n.+2 ^ m
    *)
    have -> : n.+3 ^ m - 1 - n.+2 ^ m = \sum_(1 <= k < m) 'C(m, k) * n.+2 ^ k.
      rewrite -[n.+3]addn1 addnC.
      rewrite Pascal.
      rewrite -(@big_mkord _ 0 addn m.+1 (fun n => true) (fun i => 'C(m, i) * (1 ^ (m - i) * n.+2 ^ i))).
      rewrite big_nat_recr /=; last done.
      rewrite binn exp1n !mul1n.
      rewrite big_ltn; last done.
      rewrite bin0 exp1n !mul1n expn0 [1 + _]addnC -addnA -subnDA -subnBA; last done.
      rewrite subnn subn0.
      apply: eq_big_nat => i H.
      by rewrite exp1n mul1n.
    rewrite -big_split /=.
    apply: congr_big; first done; first done.
    by move=> i _; rewrite -mulnDr -big_nat_recr.
    (* 追加ここまで *)
  Qed.

  Lemma lm_bin p k :
    2 < p ->
    1 <= k < p.-1 ->
    prime p ->
    ~~(p %| 'C(p.-1, k)).
    (*
      pが3以上の素数であり、
      kが1以上p-1未満であるなら、
      'C(p-1, k)はpで割り切れない。
    *)
  Proof.
    move=> Hpgt2 /andP [Hkgt0 Hkltpredp] Hprmp.
    rewrite bin_factd.
    - rewrite -prime_coprime; last done.
      apply/coprimeP; first by apply: (@ltn_trans 2).
      exists (((p.-1)`!.+1) %/ p, k`! * (p.-1 - k)`!) => /=.
      rewrite divnK.
      + rewrite mulnC divnK.
        * rewrite -addn1 addnC -addnBA; last done.
          by rewrite subnn.
        * rewrite -(@bin_fact p.-1 k).
          -- by apply: dvdn_mull.
          -- by rewrite leq_eqVlt; apply/orP; right.
      + by move: (Hprmp); rewrite Wilson; last by apply: (@ltn_trans 2).
    - by apply: (@ltn_trans k).
  Qed.

  Lemma lm_evn_p p :
    p > 2 ->
    prime p ->
    odd p.-1 = false.
    (*
      pが3以上の素数なら、
      p-1は奇数ではない。
    *)
  Proof.
    move=> Hpgt2 => /even_prime [Hpeq2 | Hoddp].
    - by rewrite Hpeq2 in Hpgt2.
    - apply: negbTE.
      rewrite -oddS.
      rewrite prednK; first done.
      by apply: (@ltn_trans 2 0 p).
  Qed.

  Lemma lm_div_p_tmpp_pp p :
    p > 2 ->
    \sum_(1 <= k < p.-1) 'C(p.-1, k) * Sk k p.-1 = p ^ p.-1 - p ->
    p %| \sum_(1 <= k < p.-1) 'C(p.-1, k) * Sk k p.-1.
    (*
      pが3以上で、
      \sum_(1 <= k < p.-1) 'C(p.-1, k) * Sk k p.-1 = p ^ p.-1 - pなら、
      \sum_(1 <= k < p.-1) 'C(p.-1, k) * Sk k p.-1はpで割り切れる。(当たり前)
    *)
  Proof.
    move=> Hpgt2 ->.
    apply: dvdn_sub; last done.
    apply: dvdn_exp; last done.
    rewrite ltn_predRL.
    by apply: (@ltn_trans 2 1 p).
  Qed.

  Lemma lm_div_3_tm2_2 :
    3 %| \sum_(1 <= k < 2) 'C(2, k) * Sk k 2.
    (*
      \sum_(1 <= k < 2) 'C(2, k) * Sk k 2は3で割り切れる。
    *)
  Proof.
    rewrite big_nat1 bin1 /Sk.
    have -> : (2 * \sum_(1 <= i < 3) i ^ 1) = 2 * 3.
      rewrite big_ltn; last done.
      rewrite big_ltn; last done.
      by rewrite big_nil !expn1 addn0.
    by apply: dvdn_mull.
  Qed.

  Lemma lm_div_3_tm2_2' :
    3 %| Sk 1 2.
    (*
      Sk 1 2は3で割り切れる。(定理Skpでp=3の場合)
    *)
  Proof.
    move: lm_div_3_tm2_2.
    rewrite big_ltn; last done.
    rewrite big_nil addn0.
    have H : ~~ (3 %| 'C(2, 1)) by apply: (lm_bin 3 1).
    rewrite Euclid_dvdM; last done.
    by move/orP; case.
  Qed.

  Lemma lm_sum_0_to_n n :
    2 * (\sum_(0 <= i < n.+1) i ^ 1) = n * n.+1.
    (*
      1からnまでの和は、n*(n+1)/2に等しい。
    *)
  Proof.
    elim: n => [| n IHn].
    - rewrite big_ltn; last done.
      rewrite expn1 add0n.
      by rewrite big_geq; last done.
    - rewrite big_nat_recr /=; last done.
      by rewrite mulnDr expn1 IHn -mulnDl addn2 mulnC.
  Qed.

  Lemma lm_div_p_tmpp_pp' p :
    p > 2 ->
    prime p ->
    p %| \sum_(1 <= k < p.-1) 'C(p.-1, k) * Sk k p.-1 ->
    (p %| \sum_(1 <= k < 2) 'C(p.-1, k) * Sk k p.-1)
    /\ (p %| \sum_(2 <= k < p.-1) 'C(p.-1, k) * Sk k p.-1).
    (*
      pが3以上の素数で、
      \sum_(1 <= k < p.-1) 'C(p.-1, k) * Sk k p.-1がpで割り切れるなら、
      \sum_(1 <= k < 2) 'C(p.-1, k) * Sk k p.-1と
      \sum_(2 <= k < p.-1) 'C(p.-1, k) * Sk k p.-1は
      ともにpで割り切れる。
    *)
  Proof.
    move=> Hpgt2 Hprmp.
    rewrite big_ltn; last by rewrite ltn_predRL.
    rewrite bin1.
    rewrite -{1}(@odd_double_half p.-1) lm_evn_p; last done; last done.
    rewrite -muln2 -mulnA /Sk prednK; last  by apply: (@ltn_trans 2 0 p).
    have H : 2 * (\sum_(1 <= i < p) i ^ 1) = p.-1 * p.
      move: (lm_sum_0_to_n p.-1).
      rewrite prednK; last by apply: (@ltn_trans 2 0 p).
      rewrite big_ltn; last by apply: (@ltn_trans 2 0 p).
      by rewrite expn1 add0n.
    rewrite H mulnA.
    move/dvdn_add_eq.
    rewrite dvdn_mull; last done.
    move=> <-.
    rewrite big_ltn; last done.
    rewrite bin1 -{1}(@odd_double_half p.-1) lm_evn_p; last done; last done.
    by rewrite -muln2 -mulnA /Sk H mulnA big_nil addn0 dvdn_mull.
  Qed.

  Lemma lm_div_p_tmpp_pp'' p :
    p > 2 ->
    prime p ->
    m = p.-1 ->
    p %| \sum_(1 <= k < m) 'C(m, k) * Sk k p.-1.
    (*
      pが3以上の素数であり、
      m=p-1なら、
      \sum_(1 <= k < m) 'C(m, k) * Sk k p.-1はpで割り切れる。
    *)
  Proof.
    move=> Hpgt2 Hprmp Hmeqprdp.
    move: (Tmn p.-2).
    rewrite prednK /Tm.
    - move=> ->.
      rewrite prednK; last by apply: (@ltn_trans 2 0 p).
      apply: dvdn_sub; last done.
      rewrite dvdn_exp; first done; last done.
      by apply: (@ltn_trans 1 0 m).
    - rewrite -Hmeqprdp.
      by apply: (@ltn_trans 1 0 m).
  Qed.

  Theorem Skp p k :
    p > 2 ->
    prime p ->
    1 <= k < p.-1 ->
    p %| Sk k p.-1.
    (*
      pが3以上の素数のとき、
      Sk(p-1) (1 <= k <= p-2)はpの倍数である。
    *)
  Proof.
    (* 追加ここから *)
    (* 追加ここまで *)
  Admitted.

End Nagoya2013.
