From mathcomp Require Import all_ssreflect.

Require Import Wf_nat Recdef.

Check lt_wf : well_founded lt.

(* 自己確認(ここから) *)
Check well_founded lt : Prop.
Print well_founded.
(*
well_founded = 
  fun (A : Type) (R : A -> A -> Prop) =>
    forall a : A, Acc R a
  : forall A : Type, (A -> A -> Prop) -> Prop
*)
Print Acc.
(*
Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x
*)
Check lt : nat -> nat -> Prop.
(* 自己確認(ここまで) *)

Check lt_wf_ind :
        forall (n : nat) (P : nat -> Prop),
          (forall n0 : nat, (forall m : nat, (m < n0)%coq_nat -> P m) -> P n0) ->
          P n.

Function gcd (m n : nat) {wf lt m} : nat :=
  if m is 0
  then n
  else gcd (modn n m) m.
Proof.
  - move=> m n m0 _. apply/ltP.
      by rewrite ltn_mod.
  - exact: lt_wf.
  Restart.
  (* 自己確認(ここから) *)
  - (* 本題の証明 *)
    move=> m n n0 Hm.
    Check ltP. (* : reflect (?m < ?n)%coq_nat (?m < ?n) *)
    apply/ltP.
    Check ltn_mod : forall m d : nat, (m %% d < d) = (0 < d).
    rewrite ltn_mod.
    Check ltn0Sn : forall n : nat, 0 < n.+1.
    by apply: ltn0Sn.
  - (* well_founded lt の証明 *)
    by apply: lt_wf.
  (* 自己確認(ここまで) *)
Qed.

Check gcd_equation :
  forall m n : nat,
    gcd m n = match m with
              | 0 => n
              | _.+1 => gcd (n %% m) m
              end.

Check gcd_ind :
        forall P : nat -> nat -> nat -> Prop,
          (forall m n : nat, m = 0 -> P 0 n n) ->
          (forall m n _x : nat,
             m = _x ->
             match _x with
             | 0    => False
             | _.+1 => True
             end ->
             P (n %% m) m (gcd (n %% m) m) ->
             P _x n (gcd (n %% m) m)) ->
          forall m n : nat, P m n (gcd m n).

Print gcd_terminate.
(*
  とても理解できる代物じゃない。
*)

Require Import Extraction.

Extraction gcd.                             (* wf が消える*)
(*
Fetching opaque proofs from disk for mathcomp.ssreflect.ssrnat
Fetching opaque proofs from disk for Coq.ssr.ssrbool
The extraction is currently set to bypass opacity, the following opaque constant bodies have
been accessed : eqnP iffP idP.
 [extraction-opaque-accessed,extraction]
(** val gcd : nat -> nat -> nat **)

let rec gcd m n =
  match m with
  | O -> n
  | S n0 -> gcd (modn n (S n0)) (S n0)
*)

Check divn_eq :
        forall m d : nat,
          m = m %/ d * d + m %% d.

Theorem gcd_divides m n :
  (gcd m n %| m) && (gcd m n %| n).
Proof.
  functional induction (gcd m n).
  - (* m = 0 の場合 *)
    by rewrite dvdn0 dvdnn.
  - (* m = _.+1 の場合 *)
    move: IHn0 => /andP [H1 H2].
    apply/andP; split.
    + (* gcd (n %% m) m %| m の証明 *)
      by apply: H2.
    + (* gcd (n %% m) m %| n の証明 *)
      Check divn_eq n m : n = n %/ m * m + n %% m.
      rewrite {2}(divn_eq n m).
      Check dvdn_add : forall d m n : nat, d %| m -> d %| n -> d %| m + n.
      apply: dvdn_add; last done.
      Check dvdn_mull : forall d m n : nat, d %| n -> d %| m * n.
      by apply: dvdn_mull.
Qed.

Check addKn :
        forall n : nat,
          cancel (addn n) (subn^~ n).

Check gcd_equation :
        forall m n : nat,
          gcd m n = match m with
                    | 0 => n
                    | _.+1 => gcd (n %% m) m
                    end.

Check muln_modl :
        forall p m d : nat,
          m %% d * p = (m * p) %% (d * p).

Lemma gcd_max_sub g k1 k2 :
  gcd (k1 * g) (k2 * g) = (gcd k1 k2) * g.
Proof.
  functional induction (gcd k1 k2).
  - (* k1 = 0 *)
    rewrite mul0n.
    rewrite gcd_equation.
    by [].
  - (* k1 = _.+1 *)
    rewrite -IHn.
    rewrite (@muln_modl g n m).
    rewrite gcd_equation.
    case: (m * g); last done.
    rewrite modn0.
    case: (n * g).
    + (* n * g = 0 *)
      rewrite gcd_equation.
      by [].
    + (* n * g = _.+1 *)
      move=> n'.
      rewrite gcd_equation.
      rewrite mod0n.
      rewrite gcd_equation.
      by [].
  Restart.
  functional induction (gcd k1 k2).
  - (* k1 = 0 *)
    by rewrite mul0n gcd_equation.
  - (* k1 = _.+1 *)
    rewrite -IHn (@muln_modl g n m) gcd_equation.
    case: (m * g); last done.
    rewrite modn0; case: (n * g) => [| n'].
    + (* n * g = 0 *)
      by rewrite gcd_equation.
    + (* n * g = _.+1 *)
      by rewrite gcd_equation mod0n gcd_equation.
Qed.

Theorem gcd_max g m n :
  g %| m ->
  g %| n ->
  g %| gcd m n.
Proof.
  (*
    g %| m が成り立つなら、m = k1 * g が成り立つはず。
    g %| n が成り立つなら、n = k2 * g が成り立つはず。
    m = k1 * g, n = k2 * g が成り立つなら、
    gcd m n = gcd (k1 * g) (k2 * g) = (gcd k1 k2) * g が成り立つはず。
    そうしたら、g %| gcd m n が成り立つはず。
  *)
  rewrite dvdn_eq => /eqP <-.
  rewrite dvdn_eq => /eqP <-.
  rewrite gcd_max_sub.
  by apply: dvdn_mull.
Qed.

Lemma odd_square n :
  odd n = odd (n * n).
Proof.
  rewrite oddM.
  by case (odd n).
Qed.

Lemma even_double_half n :
  ~~odd n ->
  n./2.*2 = n.
Proof.
  move=> Hnoddn.
  rewrite -[RHS]odd_double_half.
  rewrite -[LHS]add0n.
  apply/eqP.
  rewrite eqn_add2r.
  apply/eqP.
  move: Hnoddn.
  rewrite -eqb0.
  move/eqP ->.
  by [].
Qed.

(* 本定理*)

(*
まずは自然数で以下の定理を証明する．
定理1
  任意の自然数n とp について，
  n · n = 2(p · p) ならばp = 0

証明はn の関する整礎帰納法を使う．
 n = 0 のとき，p = 0
 n ̸= 0 のとき，
   n とp が偶数でなければならないので，n = 2n′, p = 2p′ とおける
   再び，n′ · n′ = 2(p′ · p′) が得られ，n′ < n
   帰納法の仮定よりp′ = 0
   すなわち，p = 0
*)

(*
Lemma main_thm_sub1 n :
  ~~ odd n -> exists k, n = k.*2.
Proof.
  move=> Hevn.
  exists (n./2).
  by rewrite (@even_double_half n); last done.
Qed.

Check even_double_half : forall n : nat, ~~ odd n -> (n./2).*2 = n.

Lemma main_thm_sub2 n :
  ~~ odd (n * n) = ~~ odd n.
Proof.
  by rewrite -odd_square.
Qed.

Check odd_square : forall n : nat, odd n = odd (n * n).
*)

Theorem main_thm (n p : nat) :
  n * n = (p * p).*2 ->
  p = 0.
Proof.
  elim/lt_wf_ind: n p => n.                 (* 整礎帰納法*)
  case: (posnP n) => [-> _ [] // | Hn IH p Hnp].
  (* 解答開始はここから *)
  move: (@odd_double (p * p)).
  rewrite -Hnp.
  move/negbT.
  rewrite -odd_square.
  move/even_double_half => Hnev. (* この時点で、(n./2).*2 = n を証明できた。 *)

  move: (Hnp).
  rewrite -Hnev.
  rewrite -{2}muln2 mulnA -[RHS]muln2.
  rewrite [(n./2).*2 * n./2]mulnC -[(n./2).*2]muln2 mulnA [n./2 * n./2 * 2]muln2.
  move/eqP.
  rewrite eqn_mul2r => /orP [H2eq0 | Hpn] //.
  move: Hpn => /eqP Hpn.
  move: (@odd_double (n./2 * n./2)).
  rewrite Hpn.
  move/negbT.
  rewrite -odd_square.
  move/even_double_half => Hpev. (* この時点で、(p./2).*2 = p を証明できた。 *)

  have H : n./2 * n./2 = (p./2 * p./2).*2.
    move: (Hpn).
    rewrite -Hpev.
    rewrite -[in RHS]muln2 [RHS]mulnA [p./2 * 2 * p./2]mulnC [p./2 * (p./2 * 2)]mulnA.
    rewrite [p./2 * p./2 * 2]muln2 -[LHS]muln2.
    move/eqP.
    rewrite eqn_mul2r => /orP [H2e0 | Hhnhp] //.
    move: Hhnhp => /eqP Hhnhp.
    rewrite Hhnhp Hpev.
    by []. (* この時点で、n./2 * n./2 = (p./2 * p./2).*2 を証明できた。 *)

  rewrite -Hpev -muln2 -[RHS](mul0n 2).
  apply/eqP.
  rewrite eqn_mul2r.
  apply/orP.
  right. (* この時点で、ゴールを p./2 == 0 に書き換えることができた。 *)

  Check (IH n./2) :
          (n./2 < n)%coq_nat ->
          forall p : nat,
            n./2 * n./2 = (p * p).*2 ->
            p = 0.

  apply/eqP/(IH n./2); last done.
  (* この時点で、ゴールを (n./2 < n)%coq_nat に書き換えることができた。 *)

  rewrite -divn2.

  Check ltP. (* : reflect (?m < ?n)%coq_nat (?m < ?n) *)
  Check ltn_Pdiv :
          forall m d : nat,
            1 < d ->
            0 < m ->
            m %/ d < m.
  Check (@ltn_Pdiv n 2) :
          1 < 2 ->
          0 < n ->
          n %/ 2 < n.

  by apply/ltP/(@ltn_Pdiv n 2).
Qed.

Lemma main_thm'_lm1 (n p : nat) :
  n * n = (p * p).*2 ->
  (n./2).*2 = n.
Proof.
  move=> Hnp.
  move: (@odd_double (p * p)).
  rewrite -Hnp => /negbT.
  by rewrite -odd_square => /even_double_half.
Qed.

Lemma main_thm'_lm2 (n p : nat) :
  n * n = (p * p).*2 ->
  p * p = (n./2 * n./2).*2.
Proof.
  move=> Hnp.
  move: (Hnp) => /main_thm'_lm1 => Hnev.
  move: (Hnp).
  rewrite -Hnev -{2}muln2 mulnA -[RHS]muln2
          [(n./2).*2 * n./2]mulnC -[(n./2).*2]muln2 mulnA
          [n./2 * n./2 * 2]muln2 => /eqP.
  rewrite eqn_mul2r => /orP [H2eq0 | Hpn] //.
  rewrite muln2 Hnev.
  by move: Hpn => /eqP.
Qed.

Theorem main_thm' (n p : nat) :
  n * n = (p * p).*2 ->
  p = 0.
Proof.
  elim/lt_wf_ind: n p => n.                 (* 整礎帰納法*)
  case: (posnP n) => [-> _ [] // | Hn IH p Hnp].
  (* 解答開始はここから *)

  (* n * n = (p * p).*2 から p * p = (n./2 * n./2).*2 を導く。 *)
  move: (@main_thm'_lm2 n p Hnp) => Hpn.

  (* p * p = (n./2 * n./2).*2 から (p./2).*2 = p を導き、
     ゴールを (p./2).*2 = 0 に書き換える。 *)
  move: (@main_thm'_lm1 p n./2 Hpn) => <-.

  (* ゴールを p./2 == 0 に書き換える。 *)
  rewrite -muln2 -[RHS](mul0n 2).
  apply/eqP; rewrite eqn_mul2r; apply/orP; right.

  (* (IH n./2) を apply することで必要になる
     命題 n./2 * n./2 = (p./2 * p./2).*2 を証明する。 *)
  move: (@main_thm'_lm2 p n./2 Hpn) => H.

  (* (IH n./2) を apply して、ゴールを (n./2 < n)%coq_nat に書き換える。 *)
  apply/eqP/(IH n./2); last done.

  (* (@ltn_Pdiv n 2) を apply して、証明を完了する。 *)
  rewrite -divn2.
  by apply/ltP/(@ltn_Pdiv n 2).
Qed.

(* 無理数*)
Require Import Reals Field.      (* 実数とそのためのfield タクティク*)

(*
定理 main_thm : n * n = (p * p).*2 -> p = 0 を使って、
√2 が無理数であることを証明する。
もしも √2 が有理数なら、ある n と p が存在し、√2 = n/p、すなわち n ^ 2 = 2 * p ^ 2 となる。
しかし上の定理から p = 0 となるので矛盾。
*)

Check INR : nat -> R.

Definition irrational (x : R) : Prop :=  (* x が有理数でないという主張の定義らしい。 *)
  forall (p q : nat),
    q <> 0 ->
    x <> (INR p / INR q)%R.

Theorem irrational_sqrt_2:
  irrational (sqrt (INR 2)).
Proof.
  rewrite /irrational /not. (* わかりやすくするために定義を展開。 *)
  move=> p q Hq Hrt. (* これにより、ゴールが False となる。 *)
  apply: (Hq). (* これにより、ゴールが q = 0 となる。 *)

  Check (main_thm p) :
          forall p0 : nat,
            p * p = (p0 * p0).*2 ->
            p0 = 0.

  apply: (main_thm p). (* これにより、ゴールが p * p = (q * q).*2 となる。 *)

  Check INR_eq :
          forall n m : nat,
            INR n = INR m ->
            n = m.

  apply: INR_eq. (* これにより、ゴールが INR (p * p) = INR (q * q).*2 となる。 *)
  rewrite -mul2n. (* これにより、ゴールが INR (p * p) = INR (2 * (q * q)) となる。 *)

  Check mult_INR :
          forall n m : nat,
            INR (n * m)%coq_nat = (INR n * INR m)%R.

  rewrite !mult_INR.
    (* これにより、ゴールが (INR p * INR p)%R = (INR 2 * (INR q * INR q))%R となる。 *)

  Check sqrt_def (INR 2) :
          (0 <= INR 2)%R ->
          (sqrt (INR 2) * sqrt (INR 2))%R = INR 2.

  rewrite -(sqrt_def (INR 2)).
  - (* 本題の証明 *)
    rewrite Hrt.
    field. (* ここで、ゴールが INR q <> 0%R に変わる模様。どうしてだろう？ *)
    have : INR q <> 0%R.
      by auto with real.
    by apply.
  - (* (0 <= INR 2)%R の証明 *)
    auto with real.
  Restart.
  move=> p q Hq Hrt.
  apply /Hq /(main_thm p) /INR_eq.
  rewrite -mul2n !mult_INR -(sqrt_def (INR 2)) ?{}Hrt; last by auto with real.
  have Hqr : INR q <> 0%R by auto with real.
    by field.
Qed.
