(**
Coq/SSReflect/MathComp による定理証明

第3章 演習問題と追加の問題、回答なし。

======

2018_09_16 @suharahiromichi
 *)

From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 問 3.1 *)

Inductive 紅白玉 :=
| 赤玉
| 白玉
.

(** 問 3.2 *)

Print list.
(*
Inductive list (A : Type) : Type :=
  nil  : seq A
| cons : A -> seq A -> seq A
*)

Definition 玉の列 := list 紅白玉.

(** 問 3.3 *)

Check nil : 玉の列.
Fail Check 赤玉      : 玉の列.
Check cons 赤玉 nil  : 玉の列.
Fail Check nil cons 赤玉 nil : 玉の列.
Check cons 白玉 (cons 赤玉 nil).

(** 問 3.4 *)
(* 次の定義を修正して、完成してください。 *)

Definition eq_ball (a b : 紅白玉) : bool :=
  match a with
  | 赤玉 =>
      match b with
      | 赤玉 => true
      | 白玉 => false
      end
  | 白玉 =>
      match b with
      | 赤玉 => false
      | 白玉 => true
      end
  end.

Fixpoint 赤数え (s : 玉の列) : nat :=
  match s with
    nil => 0
  | cons h t =>
      if eq_ball h 赤玉 then
        1 + 赤数え t
      else
        赤数え t
  end.

Compute 赤数え nil.
  (* = 0 : nat *)
Compute 赤数え (cons 赤玉 nil).
  (* = 1 : nat *)
Compute 赤数え (cons 白玉 nil).
  (* = 0 : nat *)
Compute 赤数え (cons 赤玉 (cons 赤玉 nil)).
  (* = 2 : nat *)
Compute 赤数え (cons 赤玉 (cons 白玉 (cons 赤玉 nil))).
  (* = 2 : nat *)

Definition count_rouge_with_map s :=
  sumn (map (fun m => if m is 赤玉 then 1 else 0) s).
(*
m is 赤玉　はProp型ではない点に注意
m = 赤玉 ではない
by 須原さん
*)

Compute count_rouge_with_map nil.
  (* = 0 : nat *)
Compute count_rouge_with_map (cons 赤玉 nil).
  (* = 1 : nat *)
Compute count_rouge_with_map (cons 白玉 nil).
  (* = 0 : nat *)
Compute count_rouge_with_map (cons 赤玉 (cons 赤玉 nil)).
  (* = 2 : nat *)
Compute count_rouge_with_map (cons 赤玉 (cons 白玉 (cons 赤玉 nil))).
  (* = 2 : nat *)

Definition count_rouge_with_filter s :=
  size (filter (fun m => if m is 赤玉 then true else false) s).

Compute count_rouge_with_filter nil.
  (* = 0 : nat *)
Compute count_rouge_with_filter (cons 赤玉 nil).
  (* = 1 : nat *)
Compute count_rouge_with_filter (cons 白玉 nil).
  (* = 0 : nat *)
Compute count_rouge_with_filter (cons 赤玉 (cons 赤玉 nil)).
  (* = 2 : nat *)
Compute count_rouge_with_filter (cons 赤玉 (cons 白玉 (cons 赤玉 nil))).
  (* = 2 : nat *)

Definition count_rouge_with_filter' s :=
  size (filter (eq_ball 赤玉) s).

Compute count_rouge_with_filter' nil.
  (* = 0 : nat *)
Compute count_rouge_with_filter' (cons 赤玉 nil).
  (* = 1 : nat *)
Compute count_rouge_with_filter' (cons 白玉 nil).
  (* = 0 : nat *)
Compute count_rouge_with_filter' (cons 赤玉 (cons 赤玉 nil)).
  (* = 2 : nat *)
Compute count_rouge_with_filter' (cons 赤玉 (cons 白玉 (cons 赤玉 nil))).
  (* = 2 : nat *)

Theorem thm1 :
  forall s : 玉の列,
    赤数え s = count_rouge_with_map s.
Proof.
  intro.
  induction s.
  - (* s = nil の場合 *)
    reflexivity.
  - (* s = nil でない場合 *)
    case a.
    + (* a = 赤玉の場合 *)
      simpl.
      rewrite IHs.
      reflexivity.
    + (* a = 白玉の場合 *)
      simpl.
      rewrite IHs.
      reflexivity.
Qed.

Theorem thm2 :
  forall s : 玉の列,
    赤数え s = count_rouge_with_filter s.
Proof.
  intro.
  induction s.
  - (* s = nil の場合 *)
    reflexivity.
  - (* s = nil でない場合 *)
    case a.
    + (* a = 赤玉の場合 *)
      simpl.
      rewrite IHs.
      reflexivity.
    + (* a = 白玉の場合 *)
      simpl.
      rewrite IHs.
      reflexivity.
Qed.

  
(** 問 3.5 追加の問題 *)
(** 与えられた玉の列に対する赤玉の数を示す述語 num_of_red を Inductive により定義せよ。 *)
(* 次の定義を修正して、完成してください。 *)

Inductive num_of_red : 玉の列 -> nat -> Prop :=
| b_nil   : num_of_red nil 0
| b_red   : forall s n, num_of_red s n -> num_of_red (赤玉 :: s) (1 + n)
(* 1 + n は変数で置き換えて、前提条件にする方がいい by 須原さん *)
| b_white : forall s n, num_of_red s n -> num_of_red (白玉 :: s) n
.

(** 問 3.6 追加の問題 *)
(** 命題 [num_of_red (cons 白玉 (cons 赤玉 nil)) 1] が真であることを示せ。 *)
(* Admitted を修正してください。 *)

Goal num_of_red (cons 白玉 (cons 赤玉 nil)) 1.
Proof.
  apply b_white.
  apply b_red with (s := nil) (n := 0).
  apply b_nil.
Qed.

(** 問 3.7 追加の問題 *)
(** 命題 [num_of_red (cons 白玉 (cons 赤玉 nil)) 0] が偽（否定が真）であることを示せ。 *)
(* Admitted を修正してください。 *)

Goal ~ num_of_red (cons 白玉 (cons 赤玉 nil)) 0.
Proof.
  unfold not.
  intro.
  inversion H; subst; clear H.
  inversion H1.
(*
  inversion H1; subst; clear H1.
  inversion H2.
  rewrite <- H1 in H0.
  inversion H0.
*)
Qed.

(** 問 3.8 追加の問題 *)
(** 問 3.4 で定義した 関数 赤数え の結果と、問 3.5 で定義した 述語
    num_of_red の命題が必要十分条件であることを定理として示せ。
    このとき、num_of_red の定義を見直してもよい。 *)
(* admit と Admitted を修正してください。 *)

Lemma eq_red :
  forall a : 紅白玉,
    eq_ball a 赤玉 = true -> a = 赤玉.
Proof.
  intro.
  induction a.
  - (* aが赤玉の場合 *)
    intro.
    reflexivity.
  - (* aが白玉の場合 *)
    intro.
    inversion H.
Qed.

Lemma eq_white :
  forall a : 紅白玉,
    eq_ball a 赤玉 = false -> a = 白玉.
Proof.
  intro.
  induction a.
  - (* aが赤玉の場合 *)
    intro.
    inversion H.
  - (* aが白玉の場合 *)
    intro.
    reflexivity.
Qed.

Theorem 赤数え_赤の数 s n : 赤数え s = n <-> num_of_red s n.
Proof.
  split.
  - (* Fixpoint -> Inductive *)
    intros.
    rewrite <- H; clear H.
    induction s.
    + (* nilの場合 *)
      simpl.
      apply b_nil.
    + (* consの場合 *)
      simpl.
      case_eq (eq_ball a 赤玉).
      * (* trueの場合 *)
        intros.
        apply b_red in IHs.
        apply eq_red in H.
        rewrite H.
        apply IHs.
      * (* falseの場合 *)
        intros.
        apply b_white in IHs.
        apply eq_white in H.
        rewrite H.
        apply IHs.
  - (* Inductive -> Fixpoint *)
    intros.
    induction H.
    + (* b_nilの場合 *)
      simpl.
      reflexivity.
    + (* b_redの場合 *)
      simpl.
      rewrite IHnum_of_red addnC.
      reflexivity.
    + (* b_whiteの場合 *)
      simpl.
      rewrite IHnum_of_red.
      reflexivity.
Qed.

(* END *)
