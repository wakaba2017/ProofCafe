From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
m⊥n (mとnは互いに素)となる負でない分数 m/n をすべて作りあげるきれいな方法がある。
これは、ドイツの数学者 Stern とフランスの時計工 Brocot のふたりが独立に発見したため、
Stern-Brocot 木と呼ばれている。

まず、(0/1, 1/0)の2個の分数から始め、次の操作を好きなだけ繰り返す。

　隣接する分数 m/n と m'/n' の間に (m + m')/(n + n') を挿入する。

新しい分数 (m + m')/(n + n') を m/n と m'/n' の中関数(medinant)という。

それぞれの分数は、左側にあり最も近い祖先を m/n とし、右側にあり最も近い祖先を m'/n' としたとき、
(m + m')/(n + n') となっている。
ここで、祖先というのは、枝を上にたどることによって到達できる分数のことである。

この構成方法のどの段階においても、m/n と m'/n' が隣接した分数のとき、

　m' * n - m * n' = 1　・・・　★

が成り立つ。
これは最初の段階では、

　1 * 1 - 0 * 0 = 1　・・・　★0

であり、成り立っている。
新しい中関数 (m + m')/(n + n') を挿入する前に、★が成り立っていると仮定すると、
新しい中間数 (m + m')/(n + n') を挿入すると、

　(m + m') * n - m * (n + n') = 1

と

　m' * (n + n') - (m + m') * n' = 1

が成り立つことを示さなければならない。
しかし、

　(m + m') * n - m * (n + n')
　= m * n + m' * n - m * n - m * n'
　= m' * n - m * n'
　= 1 (★により)

　m' * (n + n') - (m + m') * n' = 1
　= m' * n + m' * n' - m * n' - m' * n'
　= m' * n - m * n'
　= 1 (★により)

となって、新しい中関数を挿入する前に★が成り立てば、新しい中間数を挿入しても★が成り立つことがわかる。
従って、★0と合わせて★は木の構成法のすべての段階で常に成り立つ。
*)

Lemma lm1 :
  forall m n m' n',
    m' * n - m * n' = 1 ->
    ((m + m') * n - m * (n + n') = 1) /\ (m' * (n + n') - (m + m') * n' = 1).
Proof.
  move=> m n m' n' H.
  split.
  - (* (m + m') * n - m * (n + n') = 1 の証明 *)
    by rewrite mulnDl mulnDr subnDl.
  - (* m' * (n + n') - (m + m') * n' = 1 の証明 *)
    by rewrite mulnDr mulnDl subnDr.
Qed.

(*
数学ガールの「数学的帰納法」の問題
https://qiita.com/suharahiromichi/items/da2322993ef727728ea9
上記で説明されている、有理数を使用するためのライブラリ設定を参照させていただきました。
*)
Import GRing.Theory.         (* mulrA などを使えるようにする。 *)
Import Num.Theory.           (* unitf_gt0 などを使えるようにする。 *)
Import intZmod.              (* addz など *)
Import intRing.              (* mulz など *)
Open Scope ring_scope.       (* 環の四則演算を使えるようにする。 *)

(*
さらに、m/n < m'/n' であり、m, n, m', n' がすべて負でないとき、

　m/n < (m + m')/(n + n') < m'/n'

となることを示せる。

　(m + m') * n - m * (n + n')
　= m * n + m' * n - m * n - m * n'
　= m' * n - m * n'
　= (n * n') * (m'/n' - m/n)
　> 0 (n * n' > 0, m'/n' > m/n により)

従って、

　(m + m') * n - m * (n + n')
　= (n * (n + n')) * ((m + m')/(n + n') - m/n)
　> 0

n * (n + n') > 0 より、(m + m')/(n + n') - m/n > 0 となり、(m + m')/(n + n') > m/n が示せた。

　m' * (n + n') - (m + m') * n'
　= m' * n + m' * n' - m * n' - m' * n'
　= m' * n - m * n'
　> 0

従って、

　m' * (n + n') - (m + m') * n'
　= ((n + n') * n') * (m'/n' - (m + m')/(n + n'))
　> 0

(n + n') * n' > 0 より、m'/n' - (m + m')/(n + n') > 0 となり、m'/n' > (m + m')/(n + n') が示せた。

中関数の分数は祖先のちょうど半分のところに位置するわけではないが、祖先の間のどこかには位置している。
つまり、この構成方法は順序を保存する。
従って、同じ分数が木の別のところに出現することはない。
*)

Lemma lm2_rat :
  forall (m n m' n' : rat),
    m / n < m' / n' ->
    m > 0 ->
    n > 0 ->
    m' > 0 ->
    n' > 0 ->
    (m / n < (m + m') / (n + n')) /\ ((m + m') / (n + n') < m' / n').
Proof.
  move=> m n m' n' Hmnltm'n' Hmgt0 Hngt0 Hm'gt0 Hn'gt0.
  split.
  - (* m / n < (m + m') / (n + n') の証明 *)
    rewrite ltr_pdivr_mulr; last done.
    rewrite -{2}[n]divr1 mulf_div mulr1.
    rewrite ltr_pdivl_mulr; last by apply: addr_gt0.
    rewrite mulrDl mulrDr.
    apply: ler_lt_add; first done.
    rewrite -ltr_pdivl_mulr; last done.
    rewrite -[n']mulr1 -mulf_div mulr1.
    rewrite -ltr_pdivr_mulr; last done.
    by [].
  - (* (m + m') / (n + n') < m' / n' の証明 *)
    rewrite ltr_pdivr_mulr.
    rewrite -[n + n']divr1 mulf_div mulr1.
    rewrite ltr_pdivl_mulr; last done.
    rewrite mulrDl mulrDr.
    rewrite ltr_le_add; first done; last done.
    rewrite -ltr_pdivr_mulr; last done.
    rewrite -[n]mulr1 -mulf_div divr1.
    rewrite -ltr_pdivl_mulr; first done; last done.
    by apply: addr_gt0.
Qed.
