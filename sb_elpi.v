From mathcomp Require Import all_ssreflect.
From mathcomp Require Import all_algebra.
From elpi Require Import elpi.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* SB木のInductiveによる表現 *)
Inductive sbtree : nat -> nat -> nat -> nat -> Prop :=
  sbtInit  : sbtree 0 1 1 0
| sbtLeft  : forall m n m' n',
               sbtree m n m' n' -> sbtree m n (m + m') (n + n')
| sbtRight : forall m n m' n',
               sbtree m n m' n' -> sbtree (m + m') (n + n') m' n'.

(* (m+m')/(n+n')を作る関数 *)
Definition calc_sbnode (m n m' n' : nat) : (nat * nat) := (m + m', n + n').
Eval compute in calc_sbnode 0 1 1 0. (* = (1, 1) : nat * nat 1/1のつもり *)
Eval compute in calc_sbnode 0 1 1 1. (* = (1, 2) : nat * nat 1/2のつもり *)
Eval compute in calc_sbnode 0 1 1 2. (* = (1, 3) : nat * nat 1/3のつもり *)
Eval compute in calc_sbnode 1 3 1 2. (* = (2, 5) : nat * nat 2/5のつもり *)
Eval compute in calc_sbnode 2 5 1 2. (* = (3, 7) : nat * nat 3/7のつもり *)

Check @sbtLeft 0 1 1 0 sbtInit. (* = 1/1 *)
Check (sbtLeft (sbtLeft sbtInit)). (* = 1/3 *)

(*
  sbtree a b c d が成り立つ場合に、その証明手順を調べるElpiプログラム
    (いずれはsbtree専用autoタクティクみたいなものを作れたらと思います。)
*)
Elpi Program check_sbtree lp:{{

  pred check_sbtree o:int, o:int, o:int, o:int.

  check_sbtree 0 1 1 0 :- coq.say "apply: sbtInit. (sbtree 0 1 1 0 → No more subgoals)".

  check_sbtree A B C D :- X = A, Y = B, Z is (C - A), W is (D - B),
                          X >= 0, Y >= 0, Z >= 0, W >= 0,
                          coq.say "apply: sbtLeft. (sbtree" A B C D "→ sbtree" X Y Z W ")",
                 	        check_sbtree X Y Z W.

  check_sbtree A B C D :- X is (A - C), Y is (B - D), Z = C, W = D,
                          X >= 0, Y >= 0, Z >= 0, W >= 0,
                          coq.say "apply: sbtRight. (sbtree" A B C D "→ sbtree" X Y Z W ")",
                          check_sbtree X Y Z W.

}}.

(* (0+1)/(1+0) = 1/1 がSB木のノードかどうかの確認 *)
Elpi Query lp:{{ check_sbtree 0 1 1 0. }}.
(*
  apply: sbtInit. (sbtree 0 1 1 0 → No more subgoals)
*)

(* (0+1)/(1+1) = 1/2 がSB木のノードかどうかの確認 *)
Elpi Query lp:{{ check_sbtree 0 1 1 1. }}.
(*
  apply: sbtLeft. (sbtree 0 1 1 1 → sbtree 0 1 1 0 )
  apply: sbtInit. (sbtree 0 1 1 0 → No more subgoals)
*)

(* (0+1)/(1+1) = 1/2 がSB木のノードであることの証明 *)
Goal sbtree 0 1 1 1. (* 0/1, 1/1 -> (0+1)/(1+1) = 1/2 *)
Proof.
  apply: sbtLeft.
  by apply: sbtInit.
Qed.

(* (2+1)/(5+2) = 3/7 がSB木のノードかどうかの確認 *)
Elpi Query lp:{{ check_sbtree 2 5 1 2. }}.
(*
  apply: sbtRight. (sbtree 2 5 1 2 → sbtree 1 3 1 2 )
  apply: sbtRight. (sbtree 1 3 1 2 → sbtree 0 1 1 2 )
  apply: sbtLeft. (sbtree 0 1 1 2 → sbtree 0 1 1 1 )
  apply: sbtLeft. (sbtree 0 1 1 1 → sbtree 0 1 1 0 )
  apply: sbtInit. (sbtree 0 1 1 0 → No more subgoals)
*)

(* (2+1)/(5+2) = 3/7 がSB木のノードであることの証明 *)
Goal sbtree 2 5 1 2. (* 2/5, 1/2 -> (2+1)/(5+2) = 3/7 *)
Proof.
  apply: (@sbtRight 1 3 1 2). (* 1/3, 1/2 -> (1+1)/(3+2) = 2/5 *)
  apply: (@sbtRight 0 1 1 2). (* 0/1, 1/2 -> (0+1)/(1+2) = 1/3 *)
  apply: (@sbtLeft 0 1 1 1). (* 0/1, 1/1 -> (0+1)/(1+1) = 1/2 *)
  apply: (@sbtLeft 0 1 1 0). (* 0/1, 1/0 -> (0+1)/(1+0) = 1/1 *)
  by apply: sbtInit.
Qed.

Eval compute in 1 * 3 - 2 * 4. (* m' * n - m * n' = 0 *)
Eval compute in 1 * 5 - 2 * 2. (* m' * n - m * n' = 1 *)
Elpi Query lp:{{ check_sbtree 2 3 1 4. }}.
(*
  The elpi command check_sbtree failed without giving a specific error message.
  Please report this inconvenience to the authors of the program.

  SB木のノードでなかった場合に、エラーメッセージを表示して終了させる方法が不明です。
  (elpiで実行すれば、Failureが返ります。)
*)
