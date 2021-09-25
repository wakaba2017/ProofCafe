From mathcomp Require Import all_ssreflect.

Module Test_ssrnat.
  Fixpoint sum n :=
    if n is m.+1 then n + sum m else 0.
  
  Theorem double_sum n : 2 * sum n = n * n.+1.
  Proof.
    elim: n => [|n IHn] //=.
    rewrite -[n.+2]addn2 !mulnDr.
    rewrite addnC !(mulnC n.+1).
      by rewrite IHn.
  Qed.
End Test_ssrnat.

Check reflect.
Check orP.

Module Test_ssrbool.
  Variables a b c : bool.
  Print andb.
  
  Lemma andb_intro : a -> b -> a && b.
  Proof.
    move=> a b.
    rewrite a.
    move=> /=.
    done.
    Restart.
      by move ->.
  Qed.
  
  Lemma andbC : a && b -> b && a.
  Proof.
    case: a => /=.
      by rewrite andbT.
      done.
   Restart.
   by case: a => //= ->.
   Restart.
     by case: a; case: b.
  Qed.

  Lemma orbC : a || b -> b || a.
  Proof.
    case: a => /=.
    - by rewrite orbT.
    - by rewrite orbF.

    Restart.
    move/orP => H.
    apply/orP.
    move: H => [Ha|Hb].
    - by right.
    - by left.
      
    Restart.
      by case: a; case: b.
  Qed.
  
  Lemma test_if x : if x == 3 then x*x == 9 else x !=3.
  Proof.
    case Hx: (x == 3).
      by rewrite (eqP Hx).
      done.

    Restart.
    case: ifP.
      by move/eqP ->.
      move/negbT. done.
  Qed.
End Test_ssrbool.

Theorem avg_prod2 m n p : m+n = p+p -> (p - n) * (p - m) = 0.
Proof.
  move=> Hmn.
  have Hp0 q: p <= q -> p-q = 0.
  rewrite -subn_eq0. by move/eqP.
  suff /orP[Hpm|Hpn]: (p <= m) || (p <= n).
  - by rewrite (Hp0 m) // muln0.
  - by rewrite (Hp0 n).
    case: (leqP p m) => Hpm //=.
    case: (leqP p n) => Hpn //=.
    suff: m + n < p + p.
      by rewrite Hmn ltnn.
        by rewrite -addnS leq_add // ltnW.
Qed.

(**
### 補題に分ける例

テキストとは異なり、haveやsuffで証明する命題を補題にしてみます。
*)

Lemma Hp0 p q : p <= q -> p - q = 0.
Proof.
  rewrite -subn_eq0.
    by move/eqP.                            (* リフレクション *)
Qed.

Lemma l_mn_pp m n p : m < p -> n < p -> m + n < p + p.
Proof.
  move=> Hmp Hnp.
    by rewrite -addnS leq_add // ltnW.
Qed.

Lemma l_pm_pn p m n : m + n = p + p  -> (p <= m) || (p <= n).
Proof.
  move=> Hmn.
(*  Check leqP p m : leq_xor_gtn p m (p <= m) (m < p).*)
  Check @leP p m : reflect (p <= m)%coq_nat (p <= m).
(**
leq_xor_gtn は、p <= m が成り立つ場合と、成り立たない場合（排他的条件）で分ける命題で、
覚えておくべき補題。

leP は Standard Coqの「<=」とMathCompの「<=」のリフレクションで、
これも覚えておくとよいが、まったく別なもの。
*)
  case: (leqP p m) => Hpm //=.
  case: (leqP p n) => Hpn //=.
  move: (l_mn_pp _ _ _ Hpm Hpn).
    by rewrite Hmn ltnn.
Qed.

Theorem avg_prod2' m n p : m + n = p + p -> (p - n) * (p - m) = 0.
Proof.
  move=> Hmn.
  move: (l_pm_pn p m n Hmn).
  Check Hp0 p m : p <= m -> p - m = 0.
  Check Hp0 p n : p <= n -> p - n = 0.
  (* 答えはこのファイルの末尾にあります。 *)
  (* 勉強会時間内に書いた証明 *)
  move=> H.
  Search _ (_ * _ == 0).
  apply/eqP.
  rewrite muln_eq0.
  move/orP in H.
  case: H.
  - move/Hp0 => H.
    apply/orP.
    right.
    apply/eqP.
    by [].
  - move/Hp0 => H.
    apply/orP.
    left.
    apply/eqP.
    by [].
Qed.

Theorem avg_prod2'' m n p : m + n = p + p -> (p - n) * (p - m) = 0.
Proof.
  move=> Hmn.
  move: (l_pm_pn p m n Hmn).
  Check Hp0 p m : p <= m -> p - m = 0.
  Check Hp0 p n : p <= n -> p - n = 0.
  (* 答えはこのファイルの末尾にあります。 *)
  (* 勉強会後に盛田さんの証明を真似て、
     補題 muln_eq0 を使わずに1行にまとめてみた証明 *)
  by move/orP; case; move/Hp0 ->; [rewrite muln0 | rewrite mul0n].
Qed.

Theorem avg_prod2''' m n p : m + n = p + p -> (p - n) * (p - m) = 0.
Proof.
  move=> Hmn.
  move: (l_pm_pn p m n Hmn).
  Check Hp0 p m : p <= m -> p - m = 0.
  Check Hp0 p n : p <= n -> p - n = 0.
  (* 答えはこのファイルの末尾にあります。 *)
  (* 勉強会後に、
     無理やり補題 muln_eq0 を使って、無理やり1行にまとめてみた証明 *)
  by move/orP; case => [Hpm | Hpn]; apply/eqP; rewrite muln_eq0; apply/orP; [right | left]; apply/eqP; rewrite Hp0.
  (* 本当は8行くらいかかっている．．．(ピリオドは1個)
  by move/orP;
  case => [Hpm | Hpn];
  apply/eqP;
  rewrite muln_eq0;
  apply/orP;
  [right | left];
  apply/eqP;
  rewrite Hp0.
  *)
Qed.

(* 練習問題 1.1 *)
Module Equalities.

  Check leq_mul :
    forall m1 m2 n1 n2 : nat,
      m1 <= n1 ->
      m2 <= n2 ->
      m1 * m2 <= n1 * n2.

  Theorem square_sum a b : (a + b)^2 = a^2 + 2 * a * b + b^2.
  Proof.

    Check sqrnD :
      forall m n : nat,
        (m + n) ^ 2 = m ^ 2 + n ^ 2 + 2 * (m * n).

    rewrite sqrnD.
    rewrite -[LHS]addnA [b ^ 2 + _]addnC [LHS]addnA.
    rewrite [in LHS]mulnA.
    by [].
  (* これでは、あんまりなので、sqrnDを使わずに証明してみる。 *)
  Restart.
    rewrite [2]/(1 + 1) 3![_ ^ (1 + 1)]expnD 3!expn1.
    rewrite mulnDl 2!mulnDr.
    rewrite -[LHS]addnA [a * b + _]addnA [b * a]mulnC.
    rewrite -[in RHS]mulnA.
    rewrite [(1 + 1) * (a * b)]mulnDl mul1n.
    rewrite -[RHS]addnA.
    by [].
  Qed.

  Theorem diff_square m n : m >= n -> m^2 - n^2 = (m+n) * (m-n).
  Proof.

    Check subn_sqr :
      forall m n : nat,
        m ^ 2 - n ^ 2 = (m - n) * (m + n).

    rewrite subn_sqr [LHS]mulnC.
    by [].
  (* これでは、あんまりなので、subn_sqrを使わずに証明してみる。 *)
  Restart.
    move=> Hnlem.
    rewrite mulnDl.
    rewrite 2!mulnBr.
    rewrite -subnA.
    - (* 本筋の証明 *)
      rewrite [n * m]mulnC subKn.
      + (* 本筋の証明 *)
        by rewrite [2]/(1 + 1) 2![_ ^ (1 + 1)]expnD 2!expn1.
      + (* n * n <= m * n の証明 *)
        rewrite [m * n]mulnC leq_mul2l.
        by apply/orP; right.
    - (* n * m - n * n <= m * n の証明 *)
      rewrite [m * n]mulnC -{2}[n * m]subn0.
      by rewrite leq_sub.
    - (* m * n <= m * m の証明 *)
      rewrite leq_mul2l.
      by apply/orP; right.
  Qed.

  Theorem square_diff m n : m >= n -> (m-n)^2 = m^2 + n^2 - 2 * m * n.
  Proof.

    Check sqrnB :
      forall m n : nat,
        n <= m ->
        (m - n) ^ 2 = m ^ 2 + n ^ 2 - 2 * (m * n).

    move=> Hnlem.
    rewrite sqrnB; last by apply: Hnlem.
    by rewrite mulnA.
  (* これでは、あんまりなので、sqrnBを使わずに証明してみる。 *)
  Restart.
    move=> Hnlem.
    rewrite [2]/(1 + 1) ![_ ^ (1 + 1)]expnD !expn1.
    rewrite mulnBl !mulnBr [n * m]mulnC.
    rewrite 2![in RHS]mulnDl mul0n addn0.
    rewrite [in RHS]subnDA.
    rewrite -[in RHS]addnBAC.
    - (* 本筋の証明 *)
      rewrite -[in RHS]subnBA; first done.
      rewrite [m * n]mulnC leq_mul2l.
      by apply/orP; right.
    - (* m * n <= m * m の証明 *)
      rewrite leq_mul2l.
      by apply/orP; right.
  Qed.

End Equalities.

Lemma test x : 1 + x = x + 1.
  apply: addnC.
Abort.                           (* 定理を登録せずに証明を終わらせる*)

Lemma test x y z : x + y + z = z + y + x.
  Check etrans.
  
  Fail apply etrans.
  apply: etrans.          (* y が結論に現れないので，apply: に変える*)
  apply: etrans.
  Check f_equal.
  apply: f_equal.                           (* x + y = ?Goal0 *)
  Fail apply: addnC.
  Fail apply: addnA.

  Restart.                                 (* 証明を元に戻す*)
  rewrite addnC.                           (* rewrite も単一化を使う*)
  rewrite (addnC x).
  apply: addnA.
Abort.

Goal (forall P : nat -> Prop, P 0 -> (forall n, P n -> P (S n)) -> forall n, P n) ->
forall n m, n + m = m + n.
  move=> H n m.                             (* 全ての変数を仮定に*)
  apply: H.                                 (* n + m = 0 *)

  Restart.
  move=> H n m.
  pattern n.                       (* pattern で正しい述語を構成する*)
  apply: H.                        (* 0 + m = m + 0 *)

  Restart.
  move=> H n.                         (* forall n を残すとうまくいく*)
  apply: H.                           (* n + 0 = 0 + n *)
Abort.
