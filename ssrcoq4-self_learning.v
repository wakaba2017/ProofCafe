Require Import ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Lemma plusn0 n : n + 0 = n.
Proof.
  case: n.
  - done.
(* forall n : nat, S n + 0 = S n *)
  Restart.
  move: n.
  (**)
  Check nat_ind :
    forall P : nat -> Prop,
      P 0 ->
      (forall n : nat, P n -> P (S n)) ->
      forall n : nat, P n.
  (**)
  apply: nat_ind.                            (* elim の意味*)
  - done.
(* forall n : nat, n + 0 = n -> S n + 0 = S n *)
  (*
  - move=> n. rewrite /=. move=> ->. rewrite //.
  *)
  - move=> n /= -> //.
Qed.

(* 偶数の定義*)
Inductive even : nat -> Prop :=
| even_O : even O
| even_SS : forall n, even n -> even (S (S n)).

(* 帰納的述語を証明する定理*)
Theorem even_double n : even (n + n).
Proof.
  elim: n => /= [|n IH].
  - apply: even_O.
  - rewrite -plus_n_Sm.
      by apply: even_SS.
Qed.

(* 帰納的述語に対する帰納法もできる*)
Theorem even_plus m n : even m -> even n -> even (m + n).
Proof.
  elim: m => //=.
  Restart.
  move=> Hm Hn.
  elim: Hm => //= m' m'' IH.
    by apply: even_SS.
Qed.

(* 矛盾を導き出す*)
Theorem one_not_even : ~ even 1.
Proof.
  case.
  
  Restart.
  move H: 1 => one He.   (* move H: exp => pat はH: exp = pat を作る*)
  case: He H => //.
  
  Restart.
  move=> He.
  inversion He.
  Show Proof.      (* 証明が複雑で、SSReflect では様々な理由で避ける*)
Qed.

(* 等式を導き出す*)
Theorem eq_pred m n : S m = S n -> m = n.
Proof.
  case.                                     (* 等式を分解する*)
  done.
Qed.

Theorem contradict (P Q : Prop) : P -> ~P -> Q.
Proof. move=> p. elim. exact: p. Qed.

Module Odd.

  Inductive odd : nat -> Prop :=
  | odd_1 : odd 1
  | odd_SS : forall n, odd n -> odd (S (S n)).

  Theorem even_odd n : even n -> odd (S n).
  Proof.
    Check even_ind :
      forall P : nat -> Prop,
        P 0 ->
        (forall n : nat, even n -> P n -> P (S (S n))) ->
        forall n : nat, even n -> P n.
    Check (fun n => odd (S n)) : nat -> Prop.
    Check (@even_ind (fun n => odd (S n))) :
      odd 1 (* ★1 *) ->
      (forall n : nat, even n -> odd (S n) -> odd (S (S (S n)))) (* ★2 *) ->
      forall n : nat, even n -> odd (S n) (* ★3 *).
    apply: (@even_ind (fun n => odd (S n))).
    - (* 結果的に★1の命題を証明することになる模様。 *)
      by apply: odd_1.
    - (* 結果的に★2の命題を証明することになるらしい。 *)
      move=> n' Hevnn' HoddSn'.
      by apply: odd_SS.
    Restart.
    elim. (* 焦点の命題 even n (帰納的述語というらしい)についての帰納法
             こうすることにより、apply: (@even_ind (fun n => odd (S n))). を行っている模様。
             これにより、初期のゴールが証明され、代わりに2つの前提条件を証明することになる模様。
             (ここで、elim: n. とするとハマるので注意！) *)
    - (* 結果的に★1の命題を証明することになる模様。 *)
      by apply: odd_1.
    - (* 結果的に★2の命題を証明することになるらしい。 *)
      move=> n' Hevnn' HoddSn'.
      by apply: odd_SS.
  Qed.

  Theorem odd_even n : odd n -> even (S n).
  Proof.
    Check (@odd_ind (fun n => even (S n))) :
      even 2 (* ★1 *) ->
      (forall n : nat, odd n -> even (S n) -> even (S (S (S n)))) (* ★2 *) ->
      forall n : nat, odd n -> even (S n) (* ★3 *).
    elim.
    - (* ★1 *)
      by apply: (even_SS even_O).
    - (* ★2 *)
      move=> n' Hoddn' HevnSn'.
      by apply: even_SS.
  Qed.

  Theorem even_not_odd n : even n -> ~odd n.
  Proof.
    Check (@nat_ind (fun n => even n -> ~odd n)) :
      (even 0 -> ~ odd 0) (* ★1 *) ->
      (forall n : nat, (even n -> ~ odd n) -> even (S n) -> ~ odd (S n)) (* ★2 *) ->
      forall n : nat, even n -> ~ odd n (* ★3 *).
    elim: n.
    - (* ★1 *)
      move=> HevnO.
      by move/odd_even/one_not_even.
    - (* ★2 *)
      move=> n IHn HevnSn HoddSn.
      inversion HoddSn. (* SSReflectでは使用を避けないといけないタクティクを使ってしまった．．． *)
      + (* n = 0 *)
        rewrite -H0 in HevnSn.
        by move: one_not_even.
      + (* n > 0 *)
        apply odd_even in H0.
        rewrite H in H0.
        apply IHn in H0.
        (* inversion タクティクを使っても手詰まりになってきた．．． *)
    Restart.
    Check (@even_ind (fun n => ~odd n)) :
      ~ odd 0 (* ★1 *) ->
      (forall n : nat, even n -> ~ odd n -> ~ odd (S (S n))) (* ★2 *) ->
      forall n : nat, even n -> ~ odd n (* ★3 *).
    elim.
    - (* ★1 *)
      move/odd_even.
      by move: one_not_even.
    - (* ★2 *)
      move=> n' Hevnn' Hnoddn' HoddSSn'.
      inversion HoddSSn'. (* SSReflectでは使用を避けないといけないタクティクを使ってしまった．．． *)
      easy.
    (* 結果的に、この定理も elim: n. とするとハマるパターンの模様。 *)
  Qed.

End Odd.

Section SystemF.
  Definition Fand P Q := forall X : Prop, (P -> Q -> X) -> X.
  Definition For P Q := forall X : Prop, (P -> X) -> (Q -> X) -> X. (* andに見えるけどandではない。 *)
  Definition Ffalse := forall X : Prop, X. (* 何も証明を返さない *)
  Definition Ftrue := forall X : Prop, (X -> X). (* トートロジー、証明できるなら証明を返す *)
  Definition Feq T (x y : T) := forall P, P x <-> P y. (* ライプニッツの等式 *)
  Definition Fex T (P : T -> Prop) := forall X : Prop, (forall x, P x -> X) -> X.
  
  Theorem Fand_ok (P Q : Prop) : Fand P Q <-> P /\ Q.
  Proof.
    split => [pq | [p q] X].
    - split; by apply: pq.
    - by apply.
  Qed.
  
  (* 練習問題 *)
  Theorem For_ok (P Q : Prop) : For P Q <-> P \/ Q.
  Proof.
    split.
    - (* For P Q -> P \/ Q の証明 *)
      apply => [Hp | Hq].
      + (* Pが成り立つ場合 *)
        by left.
      + (* Qが成り立つ場合 *)
        by right.
    - (* For P Q <- P \/ Q の証明 *)
      case => [Hp | Hq] X Hpx Hqx.
      + (* Pが成り立つ場合 *)
        by apply: Hpx.
      + (* Qが成り立つ場合 *)
        by apply: Hqx.
  Qed.

  (* 練習問題 *)
  Theorem Ffalse_ok : Ffalse <-> False.
  Proof.
    split.
    - apply. (* これで1個目のゴールは消える。 *)
    - done. (* 2個目のゴールは自明。 *)
 (* split; last done.
    rewrite /Ffalse.
    by apply. *)
  Qed.

  (* 練習問題 *)
  Theorem Ftrue_ok : Ftrue <-> True.
  Proof.
    split.
    - by apply.
    - move=> _ X.
      by apply.
 (* split; first done. (* apply. move=> _. rewrite /Ftrue. move=> X. apply. *)
    by move=> _. *)
  Qed.

  (* SystemF は、古典論理ではなく、直観論理である点に注意 *)

  (* 練習問題 *)
  Theorem Feq_ok T (x y : T) : Feq x y <-> x = y.
  Proof.
    split.
    - (* Feq x y -> x = y の証明 *)
      (*
        rewrite /Feq.

        1 subgoal
        T : Type
        x, y : T
        ______________________________________(1/1)
        (forall P : T -> Prop, P x <-> P y) -> x = y

        1 subgoal
        T : Type
        x, y : T
        ______________________________________(1/1)
        forall _ : forall P : forall _ : T, Prop, iff (P x) (P y), eq x y

        Print eq. (* Inductive eq (A : Type) (x : A) : A -> Prop :=  eq_refl : x = x *)
        Print iff. (* iff = fun A B : Prop => (A -> B) /\ (B -> A) : Prop -> Prop -> Prop *)
      *)
      move=> H.
      Check eq.
      Check eq x : T -> Prop.
      Check eq y : T -> Prop.
      Check H (eq x) : x = x <-> x = y.
      Check H (eq y) : y = x <-> y = y.
      move: (H (eq x)) => H_.
      (* ゴールが同値の場合はsplit、前提が同値の場合はcaseもしくはapply/ *)
      (* 場合1 *)
      case: H_ => H1 H2.
      by apply: H1.
      (* 場合2
      apply/H_. done. *)
   (* more: (H (eq x)) => [H' H''].
      by apply: H'. *)
    - (* Feq x y <- x = y の証明 *)
      (* move=> ->. rewrite /Feq. done. *)
      by move=> ->.
  Qed.

  (* 練習問題 *)
  Theorem Fex_ok T (P : T -> Prop) : Fex P <-> exists x, P x.
  Proof.
    split.
    rewrite /Fex.
    - (* Fex P -> exists x, P x の証明 *)
      apply.  move=> x Hpx.
      by exists x.
    - (* Fex P <- exists x, P x の証明 *)
      case. move=> x Hpx X H.
      by apply: (H x).
  Qed.

  Definition Nat := forall X : Prop, (X -> X) -> X -> X.
  Definition Zero : Nat := fun X f x => x.
  Definition Succ (N : Nat) : Nat := fun X f x => f (N X f x).
  Definition Plus (M N : Nat) : Nat := fun X f x => M X f (N X f x).
  Definition Mult (M N : Nat) : Nat := fun X f x => M X (N X f) x.
  
  (* 自己確認 ここから *)
  Check Succ : Nat -> Nat.
  Eval compute in (Succ Zero).
    (*  = fun (X : Prop) (f : X -> X) (x : X) => f x : Nat *)
  Eval compute in (Succ (Succ Zero)).
    (* = fun (X : Prop) (f : X -> X) (x : X) => f (f x) : Nat *)
  (* 自己確認 ここまで *)
  
  (* こちらの定義はより直感的*)
  Definition Plus' (M N : Nat) : Nat := M Nat Succ N. (* 1 をM 回足す*)
  Definition Mult' (M N : Nat) : Nat := M Nat (Plus' N) Zero. (* N をM 回足す*)
  
  (* 自己確認 ここから *)
  Check Nat : Prop.
  Check (forall X : Prop, (X -> X) -> X -> X). (* これを M とすると．．． *)
  Check (forall Nat : Prop, (Nat -> Nat) -> Nat -> Nat). (* これが (M Nat) になると思われる。 *)
  Check Succ : Nat -> Nat. (* Plus' の場合、これが (M Nat) の第1引数になると思われる。 *)
  (* 自己確認 ここまで *)
  
  Fixpoint Nat_of_nat n : Nat := (* 自然数をNat に変換*)
    match n with
      0   => Zero
    | S m => Succ (Nat_of_nat m)
    end.
  
  (* 自己確認 ここから *)
  Eval compute in Nat_of_nat 0. (* = fun (X : Prop) (_ : X -> X) (x : X) => x : Nat *)
  Eval compute in Nat_of_nat 1. (* = fun (X : Prop) (f : X -> X) (x : X) => f x : Nat *)
  Eval compute in Nat_of_nat 2. (* = fun (X : Prop) (f : X -> X) (x : X) => f (f x) : Nat *)
  (* 自己確認 ここまで *)
  
  (* Nat の元の等価性は適用された物を比較するべき*)
  Definition eq_Nat (M N : Nat) := forall X f x, M X f x = N X f x.
  Definition eq_Nat_fun F f := forall n,
      eq_Nat (F (Nat_of_nat n)) (Nat_of_nat (f n)).
  Definition eq_Nat_op Op op := forall m n,
      eq_Nat (Op (Nat_of_nat m) (Nat_of_nat n)) (Nat_of_nat (op m n)).
  
  Theorem Succ_ok : eq_Nat_fun Succ S.
  Proof.
    rewrite /eq_Nat_fun.
    (* 自己確認 ここから
      1 subgoal
      ______________________________________(1/1)
      forall n : nat, eq_Nat (Succ (Nat_of_nat n)) (Nat_of_nat (S n))

      elim.  (* n に関する帰納法となる模様。 *)

      2 subgoals
      ______________________________________(1/2)
      eq_Nat (Succ (Nat_of_nat 0)) (Nat_of_nat 1)
      ______________________________________(2/2)
      forall n : nat,
      eq_Nat (Succ (Nat_of_nat n)) (Nat_of_nat (S n)) ->
      eq_Nat (Succ (Nat_of_nat (S n))) (Nat_of_nat (S (S n)))

      Check nat_ind :
        forall P : nat -> Prop,
        P 0 ->
        (forall n : nat, P n -> P (S n)) ->
        forall n : nat, P n.
      Check (fun n => eq_Nat (Succ (Nat_of_nat n)) (Nat_of_nat (S n))) : nat -> Prop.
      Check (nat_ind (fun n => eq_Nat (Succ (Nat_of_nat n)) (Nat_of_nat (S n)))) :
        eq_Nat (Succ (Nat_of_nat 0)) (Nat_of_nat 1) (* ★1 *) ->
        (forall n : nat,
         eq_Nat (Succ (Nat_of_nat n)) (Nat_of_nat (S n)) ->
         eq_Nat (Succ (Nat_of_nat (S n))) (Nat_of_nat (S (S n)))) (* ★2 *) ->
        forall n : nat, eq_Nat (Succ (Nat_of_nat n)) (Nat_of_nat (S n)) (* ★3 *).
    自己確認 ここまで *)
    elim.
    - (* n = 0 *)
      rewrite /Succ.
      rewrite /=.
      rewrite /Succ /Zero.
      done.
    - (* n > 0 *)
      move=> n IHn.
      rewrite /=.
      done. (* IHnを使わなくても証明できる模様。 *)
    Restart.
    by elim.
  Qed. (* 実は自明*)
  
  Theorem Plus_ok : eq_Nat_op Plus plus.
  Proof.
    rewrite /eq_Nat_op /Plus /eq_Nat.
    move=> m n X f x.
    elim: m x.
    - (* m = 0 *)
      move=> x.
      rewrite /=.
      rewrite /Zero.
      by [].
    - (* m > 0 *)
      move=> m IH x.
      rewrite /=.
      (* 自己確認 ここから
        by rewrite /Succ -IH.  (* これだけで証明完了する模様。 *)
      自己確認 ここまで *)
      (* 自己確認 ここから
        1 subgoal
        n : nat
        X : Prop
        f : X -> X
        m : nat
        IH : forall x : X, Nat_of_nat m f (Nat_of_nat n f x) = Nat_of_nat (m + n) f x
        x : X
        ______________________________________(1/1)
        Succ (Nat_of_nat m) f (Nat_of_nat n f x) = Succ (Nat_of_nat (m + n)) f x

        Check Succ_ok : eq_Nat_fun Succ S.  (* Succ_ok の中身。 *)

        eq_Nat_fun =  (* 関数を2つもらって、命題を返す関数らしい。 *)
        fun (F : Nat -> Nat) (f : nat -> nat) =>
        forall n : nat, eq_Nat (F (Nat_of_nat n)) (Nat_of_nat (f n))
             : (Nat -> Nat) -> (nat -> nat) -> Prop

        eq_Nat_fun Succ S =  (* 関数 Succ と、関数 S を渡すと、命題が返る模様。 *)
        forall n : nat, eq_Nat (Succ (Nat_of_nat n)) (Nat_of_nat (S n))
             : Prop
      自己確認 ここまで *)
      rewrite Succ_ok.  (* 左辺の Succ (Nat_of_nat m) ... を、Nat_of_nat (S m) ... に書き換える模様。 *)
      rewrite /=.  (* これを行うと、直前で行った rewrite が元に戻ってしまう模様。 *)
      rewrite [in RHS]/Succ.
      rewrite -IH.
      (* 自己確認 ここから
        rewrite /Succ.  (* こうしてみると、左辺と右辺が等しいことが自分にもわかる。 *)
      自己確認 ここまで *)
      by [].
    Restart.
    move=> m n X f x.
    elim: m x => //= m IH x.
      by rewrite Succ_ok /= [in RHS]/Succ -IH.
  Qed.
  
  Theorem Mult_ok : eq_Nat_op Mult mult.
  Proof.
    rewrite /eq_Nat_op /Mult /eq_Nat.  (* これは蛇足だが、自分にとっては必要。 *)
    move=> m n X f x.
    elim: m x => //= m IH x.
    rewrite Succ_ok.
    Check Plus_ok : eq_Nat_op Plus Nat.add.
    rewrite -[in RHS]Plus_ok.
    rewrite /Plus.
    rewrite -IH.
    rewrite /=.
    Check Succ.
    rewrite /Succ.
    done.
    Restart.
    move=> m n X f x.
    elim: m x => //= m IH x.
    by rewrite -[in RHS]Plus_ok /Plus -IH.
  Qed.

  Definition Pow (M N : Nat) := fun X => N _ (M X). (* M のN 乗*)
  Fixpoint pow m n :=
    match n with
      0   => 1
    | S n => m * pow m n
    end.

  (* 自己確認 ここから
  Eval compute in (Pow (Succ (Succ Zero)) (Succ (Succ (Succ Zero)))).
  (*
     = fun (X : Prop) (x : X -> X) (x0 : X) => x (x (x (x (x (x (x (x x0)))))))
     : forall X : Prop, (X -> X) -> X -> X

  Pow (Succ (Succ Zero)) (Succ (Succ (Succ Zero)))
  = fun X => (Succ (Succ (Succ Zero))) _ ((Succ (Succ Zero)) X)
  = fun X => (fun (X' : Prop) (x : X' -> X') (x0 : X') => x (x (x x0))) _
               ((fun (X'' : Prop) (x : X'' -> X'') (x0 : X'') => x (x x0)) X)
  = fun X => (fun (X' : Prop) (x : X' -> X') (x0 : X') => x (x (x x0))) _
               (fun (x : X -> X) (x0 : X) => x (x x0))
  ここで、
    fun (x : X -> X) (x0 : X) => x (x x0)
  を
    func2
  とでもおいてみると．．．
  = fun X => (fun (x : _ -> _) (x0 : _) => x (x (x x0))) func2
  = fun X => (fun (x0 : X) => func2 (func2 (func2 x0)))
  のようになって、x : X -> X を2回適用する関数を3回適用することになり、
  2の3乗が求められるのだろうか？
  *)
     自己確認 ここまで *)

  Lemma Nat_of_nat_eq : forall n X f1 f2 x,
      (forall y, f1 y = f2 y) ->
      @Nat_of_nat n X f1 x = @Nat_of_nat n X f2 x.
  Proof.
    move=> n X f1 f2 x H.
    elim: n.
    - (* n = 0 *)
      rewrite /=.
      rewrite /Zero.
      by [].
    - (* n > 0 *)
      move=> n IHn.
      rewrite /=.
      rewrite /Succ.
      rewrite IHn.
      by apply: H.
    Restart.
    move=> n X f1 f2 x H.
    elim: n => //= n IHn.
    by rewrite /Succ IHn H.
  Qed.
  
  Theorem Pow_ok : eq_Nat_op Pow pow.
  Proof.
    rewrite /eq_Nat_op => m n.
    rewrite /eq_Nat => X f x.
    elim: n x.
    - (* n = 0 *)
      rewrite /=.
      rewrite /Pow.
      rewrite /Succ.
      rewrite /Zero.
      done.
    - (* n > 0 *)
      move=> n IHn x.
      rewrite /=.
      rewrite -Mult_ok.
      rewrite /Mult.
      rewrite /Pow.
      rewrite /Succ.
      rewrite /Pow in IHn.
      apply: Nat_of_nat_eq => y.
      rewrite (IHn y).
      done.
    Restart.
    rewrite /eq_Nat_op => m n.
    rewrite /eq_Nat => X f x.
    elim: n x => //= n IHn x.
    rewrite /Pow in IHn.
    rewrite -Mult_ok /Mult /Pow /Succ.
    apply: Nat_of_nat_eq => y.
    by rewrite (IHn y).
  Qed.
  
  Section ProdSum.                     (* 値の対と直和も定義できます*)
    
    Variables X Y : Prop.
    Definition Prod := forall Z : Prop, (X -> Y -> Z) -> Z.
    Definition Pair (x : X) (y : Y) : Prod := fun Z f => f x y.
    Definition Fst (p : Prod) := p _ (fun x y => x).
    Definition Snd (p : Prod) := p _ (fun x y => y).
    Definition Sum := forall Z : Prop, (X -> Z) -> (Y -> Z) -> Z.
    Definition InL x : Sum := fun Z f g => f x.
    Definition InR x : Sum := fun Z f g => g x.
    
  End ProdSum.

  (* 自己確認　ここから *)
  Check Prod : (Prop -> Prop -> Prop).
  (*
  Variables X Y : Prop.
  Check Prod X Y : Prop.
  *)
  Check Pair : forall X Y : Prop, X -> Y -> Prod X Y.
  Check Fst  : forall X Y : Prop, Prod X Y -> X.
  Check Snd  : forall X Y : Prop, Prod X Y -> Y.
  Check Sum  : (Prop -> Prop -> Prop).
  (*
  Variables X Y : Prop.
  Check Sum X Y : Prop.
  *)
  Check InL  : forall X Y : Prop, X -> Sum X Y.
  Check InR  : forall X Y : Prop, Y -> Sum X Y.
  (* 自己確認　ここまで *)

  Arguments Pair [X Y]. Arguments Fst [X Y]. Arguments Snd [X Y].
  Arguments InL [X] Y. Arguments InR X [Y]. (* 型引数を省略できるようにする*)
  
  Definition Pred (N : Nat) :=         (* 前者関数の定義は工夫が必要*)
    Fst (N _ (fun p : Prod Nat Nat => Pair (Snd p) (Succ (Snd p)))
           (Pair Zero Zero)).

  (* 自己確認　ここから *)
  Check Pred : Nat -> Nat.
  Check (Pair Zero Zero) : Prod Nat Nat.
  Check (Snd (Pair Zero Zero)) : Nat.
  Check (Succ (Snd (Pair Zero Zero))) : Nat.
  Print Nat.
  (* Nat = forall X : Prop, (X -> X) -> X -> X : Prop *)
  Eval compute in Succ Zero.
  (* = fun (X : Prop) (f : X -> X) (x : X) => f x : Nat *)
  Eval compute in Succ (Succ Zero).
  (* = fun (X : Prop) (f : X -> X) (x : X) => f (f x) : Nat *)

  Eval compute in (Pred Zero).
  (* = fun (X : Prop) (_ : X -> X) (x : X) => x : Nat *)
  Eval compute in (pred 0).
  (* = 0 : nat *)

  Eval compute in (Pred (Succ Zero)).
  (* = fun (X : Prop) (_ : X -> X) (x : X) => x : Nat *)
  Eval compute in (pred (S 0)).
  (* = 0 : nat *)

  Eval compute in (Pred (Succ (Succ Zero))).
  (* = fun (X : Prop) (f : X -> X) (x : X) => f x : Nat *)
  Eval compute in (pred (S (S 0))).
  (* = 1 : nat *)
  (* 自己確認　ここまで *)

  Theorem Pred_ok : eq_Nat_fun Pred pred.
  Proof.
    rewrite /eq_Nat_fun => n.
    elim: n.
    - (* n = 0 *)
      rewrite /Pred.
      rewrite /=.
      rewrite {1}/Zero.
      rewrite /Fst /Pair.
      done.
    - (* n > 0 *)
      move=> n IHn.
      rewrite /=.
    Restart.
    (*
      ここから、須原さんの証明を真似してみたら、証明が完了した！
      凄い！
      いきなり帰納法を適用するのではなく、下ごしらえしなければいけないのがわからなかった！
      しかも、Succの定義を展開して、相当複雑な形になったのに、IHnでrewriteできるなんて、
      とても気づかない！
    *)
    case => //= n X f x.
    rewrite /Pred.
    elim: n => //= n IHn.
    rewrite /Succ.
    rewrite -IHn.
    done.
    Restart.
    case. (* nについての場合分けらしい。 *)
    - (* n = 0 *)
      rewrite /=.
      rewrite /Pred /Zero /=.
      rewrite /Pair /=.
      rewrite /Fst /=.  (* ここまでくると、左辺と右辺が等しいことが自明になる。 *)
      done.
    - (* n > 0 *)
      rewrite /=.
      move=> n X f x.
      rewrite /Pred /=.
      elim: n.
      + (* n = 0 *)
        rewrite /=.
        rewrite /Fst /Succ /Zero /Prod /Pair /=.
        rewrite /Snd /=.  (* ここまでくると、左辺と右辺が等しいことが自明になる。 *)
        done.
      + (* n > 0 *)
        rewrite /=.
        move=> n IHn.
        rewrite [RHS]/Succ.
        rewrite -IHn.  (* 左辺と右辺が、かなりよく似た形になってきた模様。 *)

        rewrite /Fst /Succ /Prod /Snd /Pair /Zero /=.
        (*
          とても複雑な式だが、同じように見える。
        *)

        done.
  Qed.
  
  (* NatをSetで定義し直したNat'を作る。 *)
  Definition Nat' := forall X : Set, (X -> X) -> X -> X.
  Check Nat' : Set.
  (* ZeroをNat'で定義し直したZero'を作る。 *)
  Definition Zero' : Nat' := fun X f x => x.
  Check Zero' : Nat'.
  (* SuccをNat'で定義し直したSucc'を作る。 *)
  Definition Succ' (N : Nat') : Nat' := fun X f x => f (N X f x).
  Check Succ' : Nat' -> Nat'.
  (* Nat_of_natをNat'で定義し直したNat_of_nat'を作る。 *)
  Fixpoint Nat_of_nat' n : Nat' := (* 自然数をNat に変換*)
    match n with
      0   => Zero'
    | S m => Succ' (Nat_of_nat' m)
    end.

  (* Nat がSet で定義されているときだけ証明可能*)
  Lemma Nat_of_nat_ok : forall n, @Nat_of_nat' n _ S O = n.
  Proof.
    elim.
    - (* n = 0 *)
      rewrite /=.
      rewrite /Zero'.
      done.
    - (* n > 0 *)
      move=> n IHn.
      rewrite /=.
      rewrite /Succ'.
      rewrite IHn.
      done.
    Restart.
    elim => //= n IHn.
    by rewrite /Succ' IHn.
  Qed.
  
End SystemF.
