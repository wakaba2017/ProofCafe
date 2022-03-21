Require Import ZArith Extraction.
From mathcomp Require Import all_ssreflect.

(***************************************)
(********** Simple Calculator **********)
(***************************************)

Module Simple.

  (** ソースコードで使用する命令語の定義 **)
  Inductive expr : Set := (* 変数を含む整数式*)
    | Cst of Z
    | Var of nat (** 変数名の代わりに、環境中の何番目かを示す自然数としている模様。 **)
    | Add of expr & expr
    | Min of expr
    | Mul of expr & expr.

  (* 自己確認ここから *)
  Print expr.
  (*
    Inductive expr : Set :=
        Cst : Z -> expr            (* 定数 *)
      | Var : nat -> expr          (* 変数 *)
      | Add : expr -> expr -> expr (* 加算 *)
      | Min : expr -> expr         (* -1倍 *)
      | Mul : expr -> expr -> expr (* 乗算 *)
  *)
  (* 自己確認ここまで *)

  (** ソースコードの実行結果を取得する関数 **)
  Fixpoint eval (env : list Z) (e : expr) : Z := (* 評価関数*)
    match e with
    | Cst x     => x
    | Var n     => nth 0 env n (* 変数の値はenv で与えられる*)
    | Add e1 e2 => eval env e1 + eval env e2
    | Min e1    => 0 - eval env e1 (** MinimumじゃなくてMinusらしい。 **)
    | Mul e1 e2 => eval env e1 * eval env e2
   end%Z.

  (* 自己確認ここから *)
  (* (x + 3) * 4 for x = 2 *)
  Eval compute in eval [:: 2%Z] (Mul (Add (Var 0) (Cst 3)) (Cst 4)).
  (*
    eval [:: 2%Z] (Mul (Add (Var 0) (Cst 3)) (Cst 4)).
  = eval [:: 2%Z] (Add (Var 0) (Cst 3)) * eval [:: 2%Z] (Cst 4).
  = (eval [:: 2%Z] (Var 0) + eval [:: 2%Z] (Cst 3)) * 4%Z.
  = (nth 0%Z [:: 2%Z] 0 + 3%Z) * 4%Z.
  = (2%Z + 3%Z) * 4%Z.
  = 20%Z.
  *)

  Eval compute in eval [::] (Cst 4). (* = 4%Z : Z *)
  Eval compute in (nth 0%Z [:: 2%Z] 0). (* = 2%Z : Z *)
  (* 自己確認ここまで *)

  (** ニーモニックの定義 **)
  Inductive code : Set := (* 逆ポーランド記法による計算譜*)
    | Cimm of Z          (** immediate **)
    | Cget of nat        (** スタックのN番目の値を上にコピーする **)
    | Cadd               (** 上の二つを足して、代わりに結果を置く **)
    | Cmin
    | Cmul.

  (** ニーモニックの実行結果を取得する関数 **)
  Fixpoint eval_code (stack : list Z) (l : list code) :=
    match l with
    | nil => stack
    | c :: l' =>
      let stack' := (* 各コマンドがスタックを変える*)
          match c, stack with
          | Cimm x, _            => x :: stack
          | Cget n, _            => nth 0 stack n :: stack (** stackのn番目をコピーして先頭にコンスしたリストを返す模様。 **)
          | Cadd  , x :: y :: st => x + y :: st
          | Cmin  , x      :: st => 0 - x :: st
          | Cmul  , x :: y :: st => x * y :: st
          | _, _ => nil
          end%Z
      in eval_code stack' l'
    end.

  (* 自己確認ここから *)
  Eval compute in eval_code [:: 2%Z] [:: Cget 0; Cimm 3; Cadd; Cimm 4; Cmul].
  (*
    = [:: 20%Z; 2%Z] : seq Z (* 実行結果がスタックのトップに積まれている。 *)
  *)
  (* 自己確認ここまで *)

  (** ソースコードをニーモニックに変換する関数 **)
  Fixpoint compile d (e : expr) : list code :=
    match e with
    | Cst x     => [:: Cimm x]
    | Var n     => [:: Cget (d+n)]
    | Add e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cadd]
    | Min e1    => compile d e1 ++ [:: Cmin]
    | Mul e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cmul]
    end.

  (* 自己確認ここから *)
  Eval compute in compile 0 (Mul (Add (Var 0) (Cst 3)) (Cst 4)).
  (*
    = [:: Cimm 4; Cimm 3; Cget 2; Cadd; Cmul] : seq code
  *)
  Eval compute in
         eval_code [:: 2%Z] (compile 0 (Mul (Add (Var 0) (Cst 3)) (Cst 4))).
  (*
    = [:: 20%Z; 2%Z] : seq Z
  *)
  (* 自己確認ここまで *)

  Lemma eval_code_cat stack l1 l2 :
    eval_code stack (l1 ++ l2) = eval_code (eval_code stack l1) l2.
    (**
        スタックの状態 : stack
        ニーモニックのリスト : l1 ++ l2
      からの実行結果は、
        スタックの状態 : eval_code stack l1
        ニーモニックのリスト : l2
      からの実行結果に等しい。
    **)
  Proof.
    (* 自己確認ここから *)
    elim: l1 stack.
    - (* l1 が空リストの場合 *)
      rewrite /=.
      reflexivity.
    - (* l1 が空リストでない場合 *)
      move=> a l IHl stack.
      rewrite cat_cons.
      case: a.
      + (* a が Cimm z の場合 *)
        move=> z.
        rewrite /=.
        by apply: IHl.
      + (* a が Cget n の場合 *)
        move=> n.
        rewrite /=.
        by apply: IHl.
      + (* a が Cadd の場合 *)
        rewrite /=.
        by apply: IHl.
      + (* a が Cmin の場合 *)
        rewrite /=.
        by apply: IHl.
      + (* a が Cmul の場合 *)
        rewrite /=.
        by apply: IHl.
    (* 自己確認ここまで *)
    Restart.
    by elim: l1 stack => //=.
  Qed.

  Theorem compile_correct e d stack : (* コンパイラの正しさ*)
    eval_code stack (compile d e) = eval (drop d stack) e :: stack.
  Proof.
    elim: e d stack => //= [n | e1 IHe1 e2 IHe2 | e IHe | e1 IHe1 e2 IHe2] d stack.
    - by rewrite nth_drop. (* e = Var n の場合 *)
    - by rewrite eval_code_cat IHe2 eval_code_cat IHe1. (* e = Add e1 e2 の場合 *)
    (* 追加ここから *)
    - (* e = Min e の場合 *)
      by rewrite eval_code_cat IHe.
    - (* e = Mul e1 e2 の場合 *)
      by rewrite 2!eval_code_cat IHe1 IHe2.
    Restart.
    (* 以下は、2017年度の coq12.pdf を自習したときに作成した証明 *)
    elim: e stack d.
    - (* e = Cst z の場合 *)
      move=> z stack d.
      by rewrite /=.
    - (* e = Var n の場合 *)
      move=> n stack d.
      by rewrite /= nth_drop.
    - (* e = Add e e0 の場合 *)
      move=> e He e0 He0 stack d.
      by rewrite 2!eval_code_cat He0 He.
    - (* e = Min e の場合 *)
      move=> e He stack d.
      by rewrite eval_code_cat He.
    - (* e = Mul e e0 の場合 *)
      move=> e He e0 He0 stack d.
      by rewrite 2!eval_code_cat He0 He.
    (* 追加ここまで *)
  Qed.

End Simple.

(******************************************)
(********** Iterating calculator **********)
(******************************************)

Module Iterator.

  (** ソースコードで使用する、演算に関する命令語の定義 **)
  Inductive expr : Set :=
    | Cst of Z
    | Var of nat
    | Add of expr & expr
    | Min of expr
    | Mul of expr & expr.

  (** ソースコード(演算に関する命令語)の実行結果を取得する関数 **)
  Fixpoint eval (env : list Z) (e : expr) : Z :=
    match e with
    | Cst x     => x
    | Var n     => nth 0 env n
    | Add e1 e2 => eval env e1 + eval env e2
    | Min e1    => 0 - eval env e1
    | Mul e1 e2 => eval env e1 * eval env e2
    end%Z.

  (** ソースコードで使用する、実行制御に関する命令語の定義 **)
  Inductive cmd : Set :=
    | Assign of nat & expr  (* env[n] に結果を入れる *)
    | Seq    of cmd & cmd   (* 順番に実行 *)
    | Repeat of expr & cmd. (* n 回繰り返す *)

  (* 追加ここから *)
  (*
    r <- 1;
    repeat (i - 1) {
                     r <- i * r;
                     i <- i - 1
                   }

    変数1 <- 1;
    repeat (変数0 - 1) {
                         変数1 <- 変数0 * 変数1;
                         変数0 <- 変数0 - 1
                       }
  *)

  (* 階乗を求めるプログラムのソースコード *)
  Definition fact :=
    Seq (Assign 1 (Cst 1))
          (* 変数1 に 1 を代入 *)
        (Repeat (Add (Var 0) (Cst (-1)))
                  (* 変数0 から 1 を引いた回数だけ次の処理を繰り返す *)
                (Seq (Assign 1 (Mul (Var 0) (Var 1)))
                       (* 変数0 に 変数1 を乗じてから 変数1 に格納する *)
                     (Assign 0 (Add (Var 0) (Cst (-1))))
                       (* 変数0 から 1 を引いてから 変数0 に格納する *)
                )
        ).
  (* 追加ここまで *)

  (** ソースコード(制御構造に関する命令語)の実行結果を取得する関数 **)
  Fixpoint eval_cmd (env : list Z) (c : cmd) : list Z :=
    match c with
    | Assign n  e  => set_nth 0%Z env n (eval env e) (** env[n] に e を評価した結果を格納する。 **)
    | Seq    c1 c2 => eval_cmd (eval_cmd env c1) c2
    | Repeat e  c  =>
      if eval env e is Zpos n (* seq のiter を使う*)
      then iter (Pos.to_nat n) (fun e => eval_cmd e c) env
      else env
    end.

  (* 自己確認ここから *)
  Eval compute in eval_cmd [:: 5%Z] fact.
  (*
    = [:: 1%Z; 120%Z] : seq Z
  *)
  (* 自己確認ここまで *)

  (** ニーモニックの定義 **)
  Inductive code : Set :=
    | Cimm of Z
    | Cget of nat
    | Cadd
    | Cmin
    | Cmul
    | Cset of nat (* スタックの上をn 番目に書き込む*)
    | Crep of nat (* 次のn 個の命令ををスタックの上分繰り返す*)
    | Cnext.      (* 終ったらCnext の後ろに跳ぶ*)

  (** ニーモニックの実行結果を取得する関数 **)
  Fixpoint eval_code (stack : list Z) (l : list code) :=
    match l with
    | nil => stack
    | c :: l' =>
      let stack' :=
          match c, stack with
          | Cimm x, _            => x :: stack
          | Cget n, _            => nth 0 stack n :: stack (* stack の n 番目をコピーして、stack の先頭に cons する。 *)
          | Cadd  , x :: y :: st => x + y :: st
          | Cmin  , x      :: st => 0 - x :: st
          | Cmul  , x :: y :: st => x * y :: st
          | Cset n, x      :: st => set_nth 0%Z st n x
          | Crep _, Zpos n :: st => iter (Pos.to_nat n) (fun st => eval_code st l') st
          | Crep _, _      :: st => st
          | Cnext , _            => stack
          | _     , _            => nil
          end%Z
      in
      match c with
      | Crep n => eval_drop n stack' l' (* Crep の後はコードを飛ばす*)
      | Cnext  => stack'                (* Cnext は評価を止める*) (* Cnextはプログラムの終わりを表す？ *)
      | _      => eval_code   stack' l' (* 他の場合は続ける*)
      end
    end
  with eval_drop n st (l : list code) := (* 相互再帰*)
    match l, n with
    | _ :: l', 0    => eval_code    st l'
    | _ :: l', S n' => eval_drop n' st l'
    | [::]   , _    => st
    end.

  Eval compute in set_nth 0 [:: 1; 2; 3] 0 10. (* = [:: 10; 2; 3] : seq nat *)
  Eval compute in set_nth 0 [:: 1; 2; 3] 1 10. (* = [:: 1; 10; 3] : seq nat *)
  Eval compute in set_nth 0 [:: 1; 2; 3] 2 10. (* = [:: 1; 2; 10] : seq nat *)
  Eval compute in set_nth 0 [:: 1; 2; 3] 3 10. (* = [:: 1; 2; 3; 10] : seq nat *)
  Eval compute in set_nth 0 [:: 1; 2; 3] 4 10. (* = [:: 1; 2; 3; 0; 10] : seq nat *)
  Eval compute in set_nth 0 [:: 1; 2; 3] 5 10. (* = [:: 1; 2; 3; 0; 0; 10] : seq nat *)

  Eval compute in nth 0 [:: 1; 2; 3] 0. (* = 1 : nat *)
  Eval compute in nth 0 [:: 1; 2; 3] 1. (* = 2 : nat *)
  Eval compute in nth 0 [:: 1; 2; 3] 2. (* = 3 : nat *)

  (** 演算に関する命令語のソースコードをニーモニックに変換する関数 **)
  Fixpoint compile d (e : expr) : list code :=
    (*
      引数 d は、引数 e が Var n だった場合、
      スタックの先頭から d + n 番目の要素をコピーして
      スタックの先頭にコンスするためのパラメータ
    *)
    match e with
    | Cst x     => [:: Cimm x]
    | Var n     => [:: Cget (d + n)]
    | Add e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cadd]
    | Min e1    => compile d e1 ++ [:: Cmin]
    | Mul e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cmul]
    end.

  (** 制御構造に関する命令語のソースコードをニーモニックに変換する関数 **)
  Fixpoint compile_cmd (c : cmd) : list code :=
    match c with
    | Assign n  e  => compile 0 e ++ [:: Cset n]
    | Seq    c1 c2 => compile_cmd c1 ++ compile_cmd c2
    | Repeat e  c  =>
        let l := compile_cmd c in
        compile 0 e ++ [:: Crep (length l)] ++ l ++ [:: Cnext]
    end.

  (* 自己確認ここから *)
  Eval compute in eval_code [:: 5%Z] (compile_cmd fact).
  (*
    = [:: 1%Z; 120%Z] : seq Z
  *)

  Eval compute in 5`!. (* = 120 : nat *)

  Eval compute in compile_cmd fact.
  (*
    = [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
          Crep 8;
            Cget 1; Cget 1; Cmul; Cset 1;
            Cimm (-1); Cget 1; Cadd; Cset 0;
          Cnext] : seq code
  *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1].
  (* = [:: 1%Z; 5%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1].
  (* = [:: 5%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1)].
  (* = [:: (-1)%Z; 5%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1].
  (* = [:: 5%Z; (-1)%Z; 5%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd].
  (* = [:: 4%Z; 5%Z; 1%Z] : seq Z *)

  Eval compute in iter 4 (fun st => eval_code st [::
                                                  Cget 1; Cget 1; Cmul; Cset 1;
                                                  Cimm (-1); Cget 1; Cadd; Cset 0;
                                                  Cnext]) [:: 5%Z; 1%Z].
  (* = [:: 1%Z; 120%Z] : seq Z *)

  (*
  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1].
  (* = [:: 5%Z; 4%Z; 5%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1].
  (* = [:: 4%Z; 5%Z; 4%Z; 5%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul].
  (* = [:: 20%Z; 4%Z; 5%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1].
  (* = [:: 4%Z; 20%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1)].
  (* = [:: (-1)%Z; 4%Z; 20%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1].
  (* = [:: 4%Z; (-1)%Z; 4%Z; 20%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd].
  (* = [:: 3%Z; 4%Z; 20%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0].
  (* = [:: 3%Z; 20%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1].
  (* = [:: 3%Z; 60%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0].
  (* = [:: 2%Z; 60%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1].
  (* = [:: 2%Z; 120%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0].
  (* = [:: 1%Z; 120%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1].
  (* = [:: 1%Z; 120%Z; 1%Z] : seq Z *)

  Eval compute in eval_code [:: 5%Z] [:: Cimm 1; Cset 1; Cimm (-1); Cget 1; Cadd;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0;
                                         Cget 1; Cget 1; Cmul; Cset 1;
                                         Cimm (-1); Cget 1; Cadd; Cset 0].
  (* = [:: 0%Z; 120%Z; 1%Z] : seq Z *)
  *)
  (* 自己確認ここまで *)

  Definition neutral c :=
    match c with
      Cnext
    | Crep _ => false
    | _      => true
    end.

  (* 自己確認ここから *)
  Eval compute in neutral Cnext.     (* = false : bool *)
  Eval compute in neutral (Crep _).  (* = false : bool *)
  (* 自己確認ここまで *)

  Inductive balanced : list code -> Prop := (* Crep とCnext の対応が取れている*)
    | Bneutral : forall c, 
                   neutral c = true ->
                   balanced [:: c]
    | Bcat     : forall l1 l2,
                   balanced l1 ->
                   balanced l2 ->
                   balanced (l1 ++ l2)
    | Brep     : forall l,
                   balanced l ->
                   balanced (Crep (length l) :: l ++ [:: Cnext]).

  Hint Constructors balanced.

  Lemma eval_drop_cat st l1 l2 :
    eval_drop (length l1) st (l1 ++ Cnext :: l2) = eval_code st l2.
  (*
    l2 に Cnext をコンスしたリストを l1 にアペンドしたリストの先頭から
    l1 の長さ分の要素を取り除いた(つまり l1 を取り除いた)リストのコマンドを
    スタック st の下で評価した結果と、
    l2 のコマンドをスタック st の下で評価した結果は等しい。
    (コマンドリストの先頭がCnextの場合、無いものと思っていい？)
  *)
  Proof.
    (* 追加ここから *)
    elim: l1.
    - by rewrite /=.
    - move=> a l IH.
      by rewrite /=.
    Restart.
    elim: l1 => //=.
    (* 追加ここまで *)
  Qed.

  Check eq_iter. (* 証明に使える*)
  (*
    eq_iter
         : forall (T : Type) (f f' : T -> T),
             f =1 f' ->
             forall n : nat, iter n f =1 iter n f'
  *)

  Eval compute in (neutral (Cimm 1)). (* = true : bool *)
  Eval compute in (neutral (Cimm 1) = true). (* = true = true : Prop *)
  Eval compute in (Bneutral (Cimm 1)) : neutral (Cimm 1) = true -> balanced [:: Cimm 1].
  Eval compute in (balanced [:: Cimm 1]). (* = balanced [:: Cimm 1] : Prop *)
  Eval compute in (balanced (compile_cmd (Assign 0 (Cst 1)))).
  (* = balanced [:: Cimm 1; Cset 0] : Prop *)

  Lemma eval_code_cat stack (l1 l2 : seq code) :
    balanced l1 ->
    eval_code stack (l1 ++ l2) =
    eval_code (eval_code stack l1) l2.
  (*
    l1 の中身について、Crep と Cnext の対応がとれているならば、
      スタックの状態 : stack
      ニーモニックのリスト : l1 ++ l2
    からの実行結果は、
      スタックの状態 : eval_code stack l1
      ニーモニックのリスト : l2
    からの実行結果に等しい。
  *)
  Proof.
    (* 追加ここから *)
    (* 追加ここまで *)
  Admitted.

  Lemma compile_balanced n e : balanced (compile n e).
  Proof.
    by elim: e n => /=; auto.
    (* 自己確認ここから *)
    Restart.
    elim: e n => /=.
    - (* e = Cimm の場合 *)
      move=> z n'.
      by apply: Bneutral.
    - (* e = Cget の場合 *)
      move=> n n0.
      by apply: Bneutral.
    - (* e = Cadd の場合 *)
      move=> e IHe e0 IHe0 n.
      apply: Bcat; first done.
      apply: Bcat; first done.
      by apply: Bneutral.
    - (* e = Cmin の場合 *)
      move=> e IHe n.
      apply: Bcat; first done.
      by apply: Bneutral.
    - (* e = Cmul の場合 *)
      move=> e IHe e0 IHe0 n.
      apply: Bcat; first done.
      apply: Bcat; first done.
      by apply: Bneutral.
    (* 自己確認ここまで *)
  Qed.

  Theorem compile_correct e d stack :
    eval_code stack (compile d e) = eval (drop d stack) e :: stack.
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq12.pdf を自習したときに作成した証明 *)
    elim: e d stack => //=.
    (* e = Cimm の場合は、 //= により証明完了。 *)
    - (* e = Cget の場合 *)
      move=> n d stack.
      by rewrite nth_drop.
    - (* e = Cadd の場合 *)
      move=> e IHe e0 IHe0 d stack.
      rewrite eval_code_cat; last by apply: compile_balanced.
      rewrite IHe0.
      rewrite eval_code_cat; last by apply: compile_balanced.
      by rewrite IHe.
    - (* e = Cmin の場合 *)
      move=> e IHe d stack.
      rewrite eval_code_cat; last by apply: compile_balanced.
      by rewrite IHe.
    - (* e = Cmul の場合 *)
      move=> e IHe e0 IHe0 d stack.
      rewrite eval_code_cat; last by apply: compile_balanced.
      rewrite IHe0.
      rewrite eval_code_cat; last by apply: compile_balanced.
      by rewrite IHe.
    (* 追加ここまで *)
  Qed.

  Lemma compile_cmd_balanced c : balanced (compile_cmd c).
  Proof.
    by elim: c => /=; auto using compile_balanced.
    (* 自己確認ここから *)
    Restart.
    (* 以下は、2017年度の coq12.pdf を自習したときに作成した証明 *)
    elim: c => /=. (* case: c => /=. では証明できない。 *)
    - (* c = Assign n e の場合 *)
      move=> n e.
      apply: Bcat; first by apply: compile_balanced.
      by apply: Bneutral.
    - (* c = Seq c c0 の場合 *)
      move=> c Hc c0 Hc0.
      by apply: Bcat.
    - (* c = Repeat e c の場合 *)
      move=> e c H.
      apply: Bcat; first by apply: compile_balanced.
      by apply: Brep.
    (* 自己確認ここまで *)
  Qed.

  Hint Resolve compile_balanced compile_cmd_balanced.

  Check compile_balanced : forall (n : nat) (e : expr), balanced (compile n e).
  Print expr.
  (*
    Inductive expr : Set :=
        Cst : Z            -> expr
      | Var : nat          -> expr
      | Add : expr -> expr -> expr
      | Min : expr         -> expr
      | Mul : expr -> expr -> expr.

    Arguments Cst _%Z_scope
    Arguments Var _%nat_scope
  *)
  Check compile : nat -> expr -> seq code.

  Check compile_cmd_balanced : forall c : cmd, balanced (compile_cmd c).
  Print cmd.
  (*
    Inductive cmd : Set :=
        Assign : nat  -> expr -> cmd
      | Seq    : cmd  -> cmd  -> cmd
      | Repeat : expr -> cmd  -> cmd.

    Arguments Assign _%nat_scope _
  *)
  Check compile_cmd : cmd -> seq code.
  Check eval_cmd : seq Z -> cmd -> seq Z.

  Check eval_code : seq Z -> seq code -> seq Z.
  Print code.
  (*
    Inductive code : Set :=
        Cimm  : Z   -> code
      | Cget  : nat -> code
      | Cadd  :        code
      | Cmin  :        code
      | Cmul  :        code
      | Cset  : nat -> code
      | Crep  : nat -> code
      | Cnext :        code.

    Arguments Cimm _%Z_scope
    Arguments Cget _%nat_scope
    Arguments Cset _%nat_scope
    Arguments Crep _%nat_scope
  *)

  Eval compute in (compile_cmd (Assign 0 (Cst 1))).
  (* = [:: Cimm 1; Cset 0] : seq code *)
  Eval compute in eval_code [:: 10%Z] (compile_cmd (Assign 0 (Cst 1))).
  (* = [:: 1%Z] : seq Z *)
  Eval compute in eval_cmd [:: 10%Z] (Assign 0 (Cst 1)).
  (* = [:: 1%Z] : seq Z *)

  Theorem compile_cmd_correct c stack :
    eval_code stack (compile_cmd c) = eval_cmd stack c.
  (*
    コマンドcをコンパイルして得られたコードのリストを、
    スタックstackの下で、
    eval_code関数で評価した結果得られたスタックの状態と、
    コマンドcをスタックstackの下で、
    eval_cmd関数で評価した結果得られたスタックの状態は等しい。
  *)
  Proof.
    (* 追加ここから *)
    elim: c stack => //=.
    - move=> n e (*stack*).
      case: e => //=.
      + move=> e e0 stack.
        rewrite !eval_code_cat; last info_auto; last done; last done.
        by rewrite !compile_correct drop0 /= drop0.
      + move=> e stack.
        rewrite !eval_code_cat; last info_auto; last done.
        by rewrite compile_correct drop0.
      + move=> e e0 stack.
        rewrite !eval_code_cat; last info_auto; last done; last done.
        by rewrite !compile_correct drop0 /= drop0.
    - move=> c IHc c0 IHc0 stack.
      rewrite eval_code_cat; last done.
      by rewrite IHc0 IHc.
    - move=> e c IHc stack.
      rewrite eval_code_cat /=; last done.
      rewrite eval_drop_cat /= compile_correct drop0.
      have -> : eval_code^~ (compile_cmd c ++ [:: Cnext]) = eval_cmd^~ c.
        move: (IHc stack).
        admit.
      by [].
    (* 追加ここまで *)
  Admitted.

(*
eval_code
  (eval_code stack (compile 0 e))
  (Crep (length (compile_cmd c)) :: compile_cmd c ++ [:: Cnext])
*)

End Iterator.

Extraction Iterator.eval_code.

(*
引数が 0 より大きければコマンドを一回だけ行うコマンド If of expr & cmd を定義せよ.
コンパイルの仕方も Repeat とほぼ同じ. それを使って整数の商を定義せよ.
*)

(******************************************)
(********** Iterating calculator 2 ********)
(******************************************)

Module Iterator2.

  (** ソースコードで使用する、演算に関する命令語の定義 **)
  Inductive expr : Set :=
    | Cst of Z
    | Var of nat
    | Add of expr & expr
    | Min of expr
    | Mul of expr & expr.

  (** ソースコード(演算に関する命令語)の実行結果を取得する関数 **)
  Fixpoint eval (env : list Z) (e : expr) : Z :=
    match e with
    | Cst x     => x
    | Var n     => nth 0 env n
    | Add e1 e2 => eval env e1 + eval env e2
    | Min e1    => 0 - eval env e1
    | Mul e1 e2 => eval env e1 * eval env e2
    end%Z.

  (** ソースコードで使用する、実行制御に関する命令語の定義 **)
  Inductive cmd : Set :=
    | Assign of nat & expr  (* env[n] に結果を入れる *)
    | Seq    of cmd & cmd   (* 順番に実行 *)
    | Repeat of expr & cmd (* n 回繰り返す *)
    | If     of expr & cmd. (* 引数が0より大きければコマンドを1回だけ行う *)

  (* 追加ここから *)
  (*
    変数1 <- 被除数;
    変数2 <- 除数;
    変数3 <- 0; ※これが商
    repeat (変数1) { ※商が最大となるのは除数が1で商が被除数の場合
                     if (変数1 - 変数2 + 1 > 0) {
                                                  変数1 <- 変数1 - 変数2;
                                                  変数3 <- 変数3 + 1
                                               }
                   }
  *)

  Definition divz :=
    Seq (Assign 3 (Cst 0))
        (Repeat (Var 0)
                (If (Add (Add (Var 0) (Cst 1)) (Min (Var 1)))
                    (Seq (Assign 0 (Add (Var 0) (Min (Var 1))))
                         (Assign 2 (Add (Var 2) (Cst 1)))
                    )
                )
        ).

  (** ソースコード(制御構造に関する命令語)の実行結果を取得する関数 **)
  Fixpoint eval_cmd (env : list Z) (c : cmd) : list Z :=
    match c with
    | Assign n  e  => set_nth 0%Z env n (eval env e) (** env[n] に e を評価した結果を格納する。 **)
    | Seq    c1 c2 => eval_cmd (eval_cmd env c1) c2
    | Repeat e  c  =>
      if eval env e is Zpos n (* seq のiter を使う*)
      then iter (Pos.to_nat n) (fun e => eval_cmd e c) env
      else env
    | If     e  c  =>
      if Z.to_nat (eval env e) > 0 (* eval env e が0未満なら、Z.to_natにより0に丸められるはず。 *)
      then eval_cmd env c (* コマンドを実行 *)
      else env (* 何もしない *)
    end.

  Eval compute in (Z.to_nat ( 2%Z)). (* = 2 : nat *)
  Eval compute in (Z.to_nat ( 1%Z)). (* = 1 : nat *)
  Eval compute in (Z.to_nat ( 0%Z)). (* = 0 : nat *)
  Eval compute in (Z.to_nat (-1%Z)). (* = 0 : nat *)
  Eval compute in (Z.to_nat (-2%Z)). (* = 0 : nat *)

  (* 自己確認ここから *)
  Eval compute in eval_cmd [:: 12%Z; 1%Z] divz. (* = [:: 0%Z; 1%Z; 12%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 2%Z] divz. (* = [:: 0%Z; 2%Z; 6%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 3%Z] divz. (* = [:: 0%Z; 3%Z; 4%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 4%Z] divz. (* = [:: 0%Z; 4%Z; 3%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 5%Z] divz. (* = [:: 2%Z; 5%Z; 2%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 6%Z] divz. (* = [:: 0%Z; 6%Z; 2%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 7%Z] divz. (* = [:: 5%Z; 7%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 8%Z] divz. (* = [:: 4%Z; 8%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 9%Z] divz. (* = [:: 3%Z; 9%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 10%Z] divz. (* = [:: 2%Z; 10%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 11%Z] divz. (* = [:: 1%Z; 11%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_cmd [:: 12%Z; 12%Z] divz. (* = [:: 0%Z; 12%Z; 1%Z; 0%Z] : seq Z *)
  (* 自己確認ここまで *)

  (** ニーモニックの定義 **)
  Inductive code : Set :=
    | Cimm of Z
    | Cget of nat
    | Cadd
    | Cmin
    | Cmul
    | Cset of nat (* スタックの上をn 番目に書き込む*)
    | Crep of nat (* 次のn 個の命令ををスタックの上分繰り返す*)
    | Cnext       (* 終ったらCnext の後ろに跳ぶ*)
    | Cif.

Locate ">".

  (** ニーモニックの実行結果を取得する関数 **)
  Fixpoint eval_code (stack : list Z) (l : list code) :=
    match l with
    | nil => stack
    | c :: l' =>
      let stack' :=
          match c, stack with
          | Cimm x, _            => x :: stack
          | Cget n, _            => nth 0 stack n :: stack (* stack の n 番目をコピーして、stack の先頭に cons する。 *)
          | Cadd  , x :: y :: st => x + y :: st
          | Cmin  , x      :: st => 0 - x :: st
          | Cmul  , x :: y :: st => x * y :: st
          | Cset n, x      :: st => set_nth 0%Z st n x
          | Crep _, Zpos n :: st => iter (Pos.to_nat n) (fun st => eval_code st l') st
          | Crep _, _      :: st => st
          | Cnext , _            => stack
          | Cif   , Zpos n :: st => 1 :: st
          | Cif   , _      :: st => 0 :: st
          | _     , _            => nil
          end%Z
      in
      match c with
      | Crep n => eval_drop n stack' l' (* Crep の後はコードを飛ばす*)
      | Cnext  => stack'                (* Cnext は評価を止める*) (* Cnextはプログラムの終わりを表す？ *)
      | _      => eval_code   stack' l' (* 他の場合は続ける*)
      end
    end
  with eval_drop n st (l : list code) := (* 相互再帰*)
    match l, n with
    | _ :: l', 0    => eval_code    st l'
    | _ :: l', S n' => eval_drop n' st l'
    | [::]   , _    => st
    end.

  (** 演算に関する命令語のソースコードをニーモニックに変換する関数 **)
  Fixpoint compile d (e : expr) : list code :=
    (*
      引数 d は、引数 e が Var n だった場合、
      スタックの先頭から d + n 番目の要素をコピーして
      スタックの先頭にコンスするためのパラメータ
    *)
    match e with
    | Cst x     => [:: Cimm x]
    | Var n     => [:: Cget (d + n)]
    | Add e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cadd]
    | Min e1    => compile d e1 ++ [:: Cmin]
    | Mul e1 e2 => compile d e2 ++ compile (S d) e1 ++ [:: Cmul]
    end.

  (** 制御構造に関する命令語のソースコードをニーモニックに変換する関数 **)
  Fixpoint compile_cmd (c : cmd) : list code :=
    match c with
    | Assign n  e  => compile 0 e ++ [:: Cset n]
    | Seq    c1 c2 => compile_cmd c1 ++ compile_cmd c2
    | Repeat e  c  =>
        let l := compile_cmd c in
        compile 0 e ++ [:: Crep (length l)] ++ l ++ [:: Cnext]
    | If     e  c  =>
        let l := compile_cmd c in
        compile 0 e ++ [:: Cif] ++ [:: Crep (length l)] ++ l ++ [:: Cnext]
    end.

  (* 自己確認ここから *)
  Eval compute in compile_cmd divz.
  (*
     = [:: Cimm 0; Cset 3;
           Cget 0;
           Crep 18;
             Cget 1; Cmin; Cimm 1; Cget 2; Cadd; Cadd;
             Cif;
               Crep 9;
                 Cget 1; Cmin; Cget 1; Cadd; Cset 0;
                 Cimm 1; Cget 3; Cadd; Cset 2;
             Cnext;
           Cnext]
     : seq code
  *)
  (* 自己確認ここまで *)

  (* 自己確認ここから *)
  Eval compute in eval_code [:: 12%Z; 1%Z] (compile_cmd divz).
  (* = [:: 0%Z; 1%Z; 12%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 2%Z] (compile_cmd divz).
  (* = [:: 0%Z; 2%Z; 6%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 3%Z] (compile_cmd divz).
  (* = [:: 0%Z; 3%Z; 4%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 4%Z] (compile_cmd divz).
  (* = [:: 0%Z; 4%Z; 3%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 5%Z] (compile_cmd divz).
  (* = [:: 2%Z; 5%Z; 2%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 6%Z] (compile_cmd divz).
  (* = [:: 0%Z; 6%Z; 2%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 7%Z] (compile_cmd divz).
  (* = [:: 5%Z; 7%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 8%Z] (compile_cmd divz).
  (* = [:: 4%Z; 8%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 9%Z] (compile_cmd divz).
  (* = [:: 3%Z; 9%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 10%Z] (compile_cmd divz).
  (* = [:: 2%Z; 10%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 11%Z] (compile_cmd divz).
  (* = [:: 1%Z; 11%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 12%Z] (compile_cmd divz).
  (* = [:: 0%Z; 12%Z; 1%Z; 0%Z] : seq Z *)
  Eval compute in eval_code [:: 12%Z; 13%Z] (compile_cmd divz).
  (* = [:: 12%Z; 13%Z; 0%Z; 0%Z] : seq Z *)
  (* 自己確認ここまで *)

End Iterator2.
