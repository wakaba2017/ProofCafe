(* 単一化*)

From mathcomp Require Import all_ssreflect.
Require String.
Import String.StringSyntax.

Open Scope string_scope.

(* 変数*)
Definition var := nat.

(* 定数・関数記号*)
Notation symbol := String.string.
Definition symbol_dec := String.string_dec.
(* 自己確認ここから *)
Check String.string_dec : forall s1 s2 : symbol, {s1 = s2} + {s1 <> s2}.
Eval compute in symbol_dec "a" "a".
(*
  = left (erefl "a")
  : {"a" = "a"} + {"a" <> "a"}
*)
(* 自己確認ここまで *)

(* 項は木構造*)
Inductive tree : Set :=
    Var : var -> tree
  | Sym : symbol -> tree
  | Fork : tree -> tree -> tree.

(* 自動的に等価性を生成する*)
Scheme Equality for tree. (* Coq 8.9 で動かないかも*)

(* Scheme Equality が失敗するなら手で定義する*)
Definition tree_eq_dec' (t1 t2 : tree) :
  {t1 = t2}+{t1 <> t2}.
Proof.
  (* 自己確認ここから *)
  revert t2; induction t1; destruct t2; try by right.
  - (* Var *)
    case /boolP: (v == v0) => /eqP H.
    + (* v = v0 *)
      by left; rewrite H.
    + (* v <> v0 *)
      by right; case.
      (*
        case で <> を展開して前提矛盾に持ち込める模様(以下同様)
      *)
  - (* Sym *)
    case (symbol_dec s s0) => H.
    + (* s = s0 *)
      by left; rewrite H.
    + (* s <> s0 *)
      by right; case.
  - (* Fork *)
    case (IHt1_1 t2_1) => [<- | N].
    + (* t1_1 = t2_1 *)
      case (IHt1_2 t2_2) => [<- | N].
      (* ここで case せずに left してしまうと証明できない *)
      * (* t1_2 = t2_2 *)
        by left.
      * (* t1_2 <> t2_2 *)
        by right; case.
    + (* t1_1 <> t2_1 *)
      by right; case.
  Restart.
  (* 自己確認ここまで *)
  revert t2; induction t1; destruct t2; try by right.
  - case /boolP: (v == v0) => /eqP H. by left; rewrite H. by right; case.
  - case (symbol_dec s s0) => H. by left; rewrite H. by right; case.
  - case (IHt1_1 t2_1) => [<-|N]; last by right; case.
  case (IHt1_2 t2_2) => [<-|N']. by left. by right; case.
Defined.

(* tree をeqType として登録する*)
Lemma tree_eq_boolP :
  Equality.axiom tree_eq_dec.
Proof.
  (*
    Equality.axiom (T:=tree) (fun x y : tree => tree_eq_dec x y)
  *)

  Check Equality.axiom : forall T : Type, rel T -> Type.
  Print Equality.axiom.
  (*
    Equality.axiom = 
      fun (T : Type) (e : rel T) => forall x y : T, reflect (x = y) (e x y)
           : forall T : Type, rel T -> Type
  *)
  Check tree_eq_dec : forall x y : tree, {x = y} + {x <> y}.
  Check @Equality.axiom tree tree_eq_dec : Type.

  move=> x y.
  case: tree_eq_dec => //= H; by constructor.
Qed.

Definition tree_eq_mixin :=
  EqMixin tree_eq_boolP.

Canonical tree_eqType :=
  Eval hnf in EqType _ tree_eq_mixin.

(* [t/x] t' *)
Fixpoint subs (x : var) (t t' : tree) : tree :=
  match t' with
  | Var v      => if v == x
                  then t
                  else t'
  | Sym b      => Sym b
  | Fork t1 t2 => Fork (subs x t t1) (subs x t t2)
  end.
(* 自己確認ここから *)
(*
  関数subsは、第3引数のツリーt'が
  ・変数だった場合：変数番号が第1引数xに等しかったら、t'をtに置き換えたものを返し、xに等しくなかったらそのまま返す。
  ・シンボルだった場合：そのまま返す。
  ・Forkだった場合：2つの枝t1,t2それぞれを第3引数として、再帰的に関数subsを繰り返し、その結果を2つの枝として持つForkを返す。
  という様な関数らしい。
*)
Eval compute in subs 1 (Sym "a") (Var 1). (* = Sym "a" : tree *)
Eval compute in subs 1 (Sym "a") (Var 2). (* = Var 2 : tree *)
(* 自己確認ここまで *)

(* 代入は変数代入の繰り返し*)
Definition subs_list (s : list (var * tree)) t : tree :=
  foldl (fun t (p : var * tree) => subs p.1 p.2 t) t s.
(* 自己確認ここから *)
(*
  subs_listは、第2引数のツリーtに含まれる各変数について、第1引数の変数とツリーのタプルのリストを順番に参照して、
  変数番号に対応するツリーに置き換える処理を表すらしい。
*)
Eval compute in subs_list [:: (0, Var 2); (1, Var 4)] (Var 0).
(*
  = Var 2 : tree  (* 変数0に割り当てられているのは「Var 2」ということらしい。 *)
 *)
Eval compute in subs_list [:: (0, Var 2); (1, Var 4)] (Var 1).
(*
  = Var 4 : tree  (* 変数1に割り当てられているのは「Var 4」ということらしい。 *)
*)
Eval compute in subs_list [:: (0, Var 2); (1, Var 4)] (Var 2).
(*
  = Var 2 : tree  (* 変数2に割り当てられているtreeは存在しないため、変数2のままということらしい。 *)
*)
Eval compute in subs_list [:: (0, Sym "a"); (1, Sym "b")] (Var 0).
(*
  = Sym "a" : tree  (* 変数0に割り当てられているのは「Sym "a"」ということらしい。 *)
*)
Eval compute in subs_list [:: (0, Sym "a"); (1, Sym "b")] (Var 1).
(*
  = Sym "b" : tree  (* 変数1に割り当てられているのは「Sym "b"」ということらしい。 *)
*)
Eval compute in subs_list [:: (0, Sym "a"); (1, Sym "b")] (Var 2).
(*
  = Var 2 : tree  (* 変数2に割り当てられているtreeは存在しないため、変数2のままということらしい。 *)
*)
Eval compute in subs_list [:: (0, Fork (Var 1) (Var 2)); (1, Fork (Var 3) (Var 4))] (Var 0).
(*
  = Fork (Fork (Var 3) (Var 4)) (Var 2) : tree
  (* 変数0に割り当てられているのは「Fork (Var 1) (Var 2)」であり、
     変数1に割り当てられているのは「Fork (Var 3) (Var 4)」であるため、
     最終的に「Fork (Fork (Var 3) (Var 4)) (Var 2)」になるということらしい。 *)
*)
Eval compute in subs_list [:: (0, Fork (Var 1) (Var 2)); (1, Fork (Var 3) (Var 4))] (Var 1).
(*
  = Fork (Var 3) (Var 4) : tree  (* 変数1に割り当てられているのは「Fork (Var 3) (Var 4)」ということらしい。 *)
*)
Eval compute in subs_list [:: (0, Fork (Var 1) (Var 2)); (1, Fork (Var 3) (Var 4))] (Var 2).
(*
  = Var 2 : tree  (* 変数2に割り当てられているtreeは存在しないため、変数2のままということらしい。 *)
*)
Eval compute in subs_list [:: (0, Fork (Var 1) (Var 2)); (1, Fork (Var 3) (Var 4))] (Var 3).
(*
  = Var 3 : tree  (* 変数3に割り当てられているtreeは存在しないため、変数3のままということらしい。 *)
*)
Eval compute in subs_list [:: (0, Fork (Var 1) (Var 2)); (1, Fork (Var 3) (Var 4))] (Var 4).
(*
  = Var 4 : tree  (* 変数4に割り当てられているtreeは存在しないため、変数4のままということらしい。 *)
*)
(* 自己確認ここまで *)

(* 単一子の定義*)
Definition unifies s (t1 t2 : tree) :=
  subs_list s t1 = subs_list s t2.
(* 例: (a, (x, y)) [x := (y, b)] [y := z] = (a, ((z,b), z)) *)
(* 自己確認ここから *)
(*
  unifiesは、第1引数の変数とツリーのタプルのリストsの元で、第2第3引数のツリーt1,t2の変数を対応するツリーに置き換えたものは等しいという命題を表すらしい。
*)
Eval compute in
    unifies
      [:: (0, Fork (Var 1) (Sym "b")); (1, Var 2)]
      (Fork (Sym "a") (Fork (Var 0) (Var 1)))
      (Fork (Sym "a") (Fork (Fork (Var 1) (Sym "b")) (Var 2))).
(*
  = Fork (Sym "a") (Fork (Fork (Var 2) (Sym "b")) (Var 2)) =
    Fork (Sym "a") (Fork (Fork (Var 2) (Sym "b")) (Var 2))
  : Prop
*)
(* 自己確認ここまで *)
Definition atree :=
  Fork (Sym "a") (Fork (Var 0) (Var 1)).
Definition asubs :=
  (0, Fork (Var 1) (Sym "b")) :: (1, Var 2) :: nil.
Eval compute in subs_list asubs atree.
(*
  = Fork (Sym "a") (Fork (Fork (Var 2) (Sym "b")) (Var 2)) : tree
 *)
(* 自己確認ここから *)
(*
  Check asubs : seq (nat * tree).
*)
(*
  Fork (Sym "a") (Fork (Var 0) (Var 1))
  ↓
  Fork (Sym "a") (Fork (Fork (Var 1) (Sym "b")) (Var 1)))
  ↓
  Fork (Sym "a") (Fork (Fork (Var 2) (Sym "b")) (Var 2)))
  となる模様。
*)
(* 自己確認ここまで *)

(* 和集合*)
Fixpoint union (vl1 vl2 : list var) :=
  if vl1 is v :: vl
  then
    if v \in vl2
    then union vl vl2
    else union vl (v :: vl2)
  else vl2.
(* 自己確認
  関数unionは、リストvl1とvl2を、要素の重複をなくしながら、1つのリストにマージして返す関数らしい。
*)

Lemma in_union_or v vl1 vl2 :
  v \in union vl1 vl2 = (v \in vl1) || (v \in vl2).
(*
  変数vが、変数のリストvl1,vl2の和集合に含まれるかどうかの真偽値と、
  変数vが変数のリストvl1に含まれるかどうかの真偽値と変数vが変数のリストvl2に含まれるかどうかの真偽値の論理和は等しい。
*)
Proof.
  elim: vl1 vl2 => //= x vl IH vl2.
  (*
    vl1 に関する帰納法( vl2 を汎化)
    vl1 が空リストの場合は try done により証明完了
    vl1 が空リストでない( vl1 = x :: vl となる)場合
    ゴールは
    (v \in (if x \in vl2 then union vl vl2 else union vl (x :: vl2))) =
    (v \in x :: vl) || (v \in vl2)
    となる。
    ゴールの左辺は
    x \in vl2 なら v \in union vl vl2
    x \notin vl2 なら v \in union vl (x :: vl2)
    ↓
    (head vl1) \in vl2 なら v \in union (tail vl1) vl2
    (head vl1) \notin vl2 なら v \in union (tail vl1) ((head vl1) :: vl2)
    を意味する模様。
  *)
  (* 追加ここから *)
  rewrite in_cons.
  (*
    ゴールの右辺を
    (v == x) || (v \in vl) || (v \in vl2)
    に書き換え
  *)
  case: ifP => Hx; rewrite IH /=.
  (*
    (x \in vl2) = true or false で場合分け
    if then else が展開されて現れた union vl _ を仮定 IH を使って書き換え
  *)
  - (* (x \in vl2) = true の場合 *)
    case Hv : (v == x) => //=.
    (*
      (v == x) = true or false で場合分け
      (v == x) = false の場合は try done で証明完了
      (v == x) = true の場合
      ゴールは
      (v \in vl) || (v \in vl2) = true
      となる。
      v = x が成り立つので、仮定の x \in vl2 を使えば証明できる。
    *)
    move: Hv => /eqP ->.
    rewrite Hx.
    by apply: orbT.
  - (* (x \in vl2) = false の場合 *)
    by rewrite in_cons Bool.orb_assoc [(v \in vl) || (v == x)]orbC.
  (* 追加ここまで *)
Qed.

(* 完全性のために必要*)
Lemma uniq_union vl1 vl2 :
  uniq vl2 ->
  uniq (union vl1 vl2).
(*
  変数のリストvl2の要素が重複していなければ、変数のリストvl1とvl2の和集合の要素は重複していない。
*)
Proof.
  elim: vl1 vl2 => //=.
  (* 追加ここから *)
  move=> x vl IH vl2 H.
  case: ifP => H'.
  - by apply: (@IH vl2 H).
  - apply: IH.
    rewrite /=.
    move: H' => /negbT H'.
    by apply/andP.
  (* 追加ここまで *)
Qed.

Search _ (uniq _).

(* 出現変数*)
Fixpoint vars (t : tree) : list var :=
  match t with
  | Var x      => [:: x]
  | Sym _      => nil
  | Fork t1 t2 => union (vars t1) (vars t2)
  end.
(* 自己確認ここから *)
(*
  関数varsは、第1引数のツリーtに含まれる変数の番号を、重複をなくしたリストにして返す関数らしい。
*)
Print atree.
(* atree = Fork (Sym "a") (Fork (Var 0) (Var 1)) : tree *)
Eval compute in vars atree.
(* = [:: 0; 1] : seq var *)
(* 自己確認ここまで *)

(* 出現しない変数は代入されない*)
Lemma subs_same v t' t :
  v \notin (vars t) ->
  subs v t' t = t.
(*
  変数vが、ツリーtに含まれる変数のリストに含まれていないならば、
  ツリーtの変数vをツリーt'で置き換えようとしても、結果はtのままである。
*)
Proof.
  elim: t => //= [x | t1 IH1 t2 IH2].
  - by rewrite inE eq_sym => /negbTE ->.
  - by rewrite in_union_or negb_or => /andP[] /IH1 -> /IH2 ->.
Qed.

Definition may_cons (x : var) (t : tree) r :=
  omap (cons (x,t)) r.
(* 自己確認ここから *)
(*
  may_consは、変数xとツリーtのタプルをリストにコンスする関数とリストrをomapに渡す処理を表す模様。
  リストrの型が(var * tree)ならSome、そうでなければNoneということ？
*)
(*
  Check omap
        : forall aT rT : Type,
            (aT -> rT) ->
            option aT ->
            option rT.

  Inductive option (A : Type) : Type :=
    Some : A -> option A
  | None : option A.

  ※optionって、HaskellでのMaybeみたいなもの？
*)
(* 自己確認ここまで *)

Definition subs_pair x t (p : tree * tree) :=
  (subs x t p.1, subs x t p.2).
(* 自己確認ここから *)
(*
  subs_pairは、タプルpの第1要素の変数xをツリーtに置き換えたものを第1要素、タプルの第2要素の変数xをツリーtに置き換えたものを第2要素とするタプルを表す模様。
*)
(* 自己確認ここまで *)

(* 単一化*)
Section Unify1.

  (* 代入を行ったときの再帰呼び出し*)
  Variable unify2 : list (tree * tree) -> option (list (var * tree)).
  (* 自己確認ここから *)
  (*
    unify2は変数名ということだが、型は関数型となる模様。
  *)
  (* 自己確認ここまで *)

  (* 代入して再帰呼び出し. x はt に現れてはいけない*)
  Definition unify_subs x t r :=
    if x \in vars t
    then None
    else may_cons x t (unify2 (map (subs_pair x t) r)).
  (* 自己確認ここから *)
  (*
    unify_subは、
    変数xがツリーtに含まれていればNoneを返し、
    変数xがツリーtに含まれていれば、変数xとツリーtのタプルをリストにコンスする関数と
    リスト(unify2 (map (subs_pair x t) r))をomapに渡して処理した結果を返す処理を表すらしい。
      (subs_pair x t)は、2要素のタプル(2要素ともツリー)を受け取って、
      タプルの各要素の変数xをツリーtで置き換えたタプル((tree * tree)型)を返す関数らしい。
      (map (subs_pair x t) r)は、
      (list (tree * tree))型のリストrに対して(subs_pair x t)を適用した結果得られる(list (tree * tree))型のリストとなる模様。
      (unify2 (map (subs_pair x t) r))は、option (list (var * tree))型となる模様。

    Check unify_subs : nat_eqType -> tree -> seq (tree * tree) -> option (seq (var * tree)).
      x : nat_eqType
      t : tree
      r : seq (tree * tree)
  *)
  (* 自己確認ここまで *)

  (* 代入をせずに分解*)
  Fixpoint unify1 (h : nat) (l : list (tree * tree)) : option (list (var * tree)) :=
    if h is h'.+1
    then
      match l with
      | nil
          => Some nil
      | (Var x, Var x') :: r
          => if x == x'
             then unify1 h' r
             else unify_subs x (Var x') r
             (*
               リストlの先頭が(Var x, Var x')の場合、
               x = x'なら、hを減らして、リストの残りrについてunify1を再帰的に実行する。
               x = x'でないなら、リストの残りrについてツリーの中の変数xを(Var x')で置き換える。
             *)
      | (Var x, t) :: r
          => unify_subs x t r
             (*
               リストlの先頭が(Var x, t)の場合、
               リストの残りrについてツリーの中の変数xをツリーtで置き換える。
             *)
      | (t, Var x) :: r
          => unify_subs x t r
             (*
               リストlの先頭が(t, Var x)の場合、
               リストの残りrについてツリーの中の変数xをツリーtで置き換える。
             *)
      | (Sym b, Sym b') :: r
          => if symbol_dec b b'
             then unify1 h' r
             else None
             (*
               リストlの先頭が(Sym b, Sym b')の場合、
                b = b'なら、hを減らして、リストの残りrについてunify1を再帰的に実行する。
                b = b'でないなら、Noneを返す。
             *)
      | (Fork t1 t2, Fork t1' t2') :: r
          => unify1 h' ((t1, t1') :: (t2, t2') :: r)
          (*
            リストlの先頭が(Fork t1 t2, Fork t1' t2')の場合、
            hを減らして、リストの残りrの前にリスト[:: (t1, t1'); (t2, t2')]をコンスしたリストについてunify1を再帰的に実行する。
          *)
      | _
          => None
          (*
            リストlが空リストでなくて先頭が上記以外の場合、Noneを返す。
          *)
      end
    else
      None.
      (*
        hが0の場合、Noneを返す。
      *)
  (*
    関数unify1は、
    第1引数が0ならNoneを返し、
    第1引数が1以上なら第2引数のリストl(list (tree * tree)型)の内容に応じた結果を返す様な関数。
    リストlの各要素のタプルに含まれるツリー同士を等しくするための(変数, ツリー)のタプルのリストを求めている？
  *)

End Unify1.

(* 等式の大きさの計算*)
Fixpoint size_tree (t : tree) : nat :=
  if t is Fork t1 t2
  then 1 + size_tree t1 + size_tree t2
  else 1.
(* 自己確認
  size_treeは、ツリーtのノードとリーフの合計数を返す関数らしい。
*)

Definition size_pairs (l : list (tree * tree)) :=
  sumn [seq size_tree p.1 + size_tree p.2 | p <- l].
(* 自己確認
  size_pairsは、リストlに含まれるタプルの要素であるツリーのノードとリーフの総数を求めて返る関数らしい。
*)

(* 代入したときだけ再帰*)
Fixpoint unify2 (h : nat) l :=
  if h is h'.+1
  then unify1 (unify2 h') (size_pairs l + 1) l
  else None.
(* 自己確認ここから *)
(*
  関数unify2は、
  第1引数hが0ならNoneを返し、
  第1引数hが1以上なら、hを1減らして、第2引数のリストlに対して関数unify1を適用する関数？
*)
Check unify2 : nat -> seq (tree * tree) -> option (seq (var * tree)).
(*
  h : nat
  l : seq (tree * tree)
*)
Check unify1 : (seq (tree * tree) -> option (seq (var * tree))) -> nat -> seq (tree * tree) -> option (seq (var * tree)).
(*
         (unify2 h') : (seq (tree * tree) -> option (seq (var * tree)))
  (size_pairs l + 1) : nat
                   l : seq (tree * tree)
*)
(* 自己確認ここまで *)

Fixpoint vars_pairs (l : list (tree * tree)) : list var :=
  match l with
  | nil => nil (* 集合を後部から作るようにする*)
  | (t1, t2) :: r => union (union (vars t1) (vars t2)) (vars_pairs r)
  end.
(* 自己確認ここから *)
(*
  関数vars_pairsは、引数のリストlの各要素に含まれるツリーの変数のリストを作成して返す関数らしい。
*)
(* 自己確認ここまで *)

(* 変数の数だけunify2 を繰り返す*)
Definition unify t1 t2 :=
  let l := [:: (t1, t2)]
  in unify2 (size (vars_pairs l) + 1) l.
(* 自己確認ここから *)
(*
  unifyは、第1引数t1と第2引数t2に含まれる変数の数だけ、タプル(t1, t2)に関数unify2を再帰的に適用する処理を表すらしい。
*)
(* 自己確認ここまで *)

(* 例*)
Eval compute in unify (Sym "a") (Var 1).
(*
  = Some [:: (1, Sym "a")] : option (seq (var * tree))

  変数1に(Sym "a")を対応させる模様。
*)
Eval compute in
  unify (Fork (Sym "a") (Var 0)) (Fork (Var 1) (Fork (Var 1) (Var 2))).
(*
  = Some [:: (1, Sym "a"); (0, Fork (Sym "a") (Var 2))] : option (seq (var * tree))

  Fork (Sym "a") (Var 0)
  Fork (Var 1)   (Fork (Var 1) (Var 2))
  の様に単一化させるらしいことから、
  変数1に(Sym "a")が割り当てられ、
  変数0に(Fork (Var 1) (Var 2))が割り当てられる模様。
  そして、変数1は(Sym "a")だから、変数0は(Fork (Sym "a") (Var 2))となる模様。
*)

(* 全ての等式の単一子*)
Definition unifies_pairs s (l : list (tree * tree)) :=
  forall t1 t2,
    (t1,t2) \in l ->
    unifies s t1 t2.
(* 自己確認
  ツリーt1,t2のタプル(t1,t2)がリストlに含まれていれば、
  sの元で、t1とt2を等しくできるという命題を表している？
*)

(* subs_list とFork が可換*)
Lemma subs_list_Fork s t1 t2 :
  subs_list s (Fork t1 t2) = Fork (subs_list s t1) (subs_list s t2).
Proof.
  elim: s t1 t2 => //.
  (* 追加ここから *)
  move=> x vl IH t1 t2 /=.
  by rewrite IH.
  (* 追加ここまで *)
Qed.

(* unifies_pairs の性質*)
Lemma unifies_pairs_same s t l :
  unifies_pairs s l -> unifies_pairs s ((t,t) :: l).
Proof.
  move=> H t1 t2; rewrite inE => /orP[].
  (* 追加ここから *)
  - (* (t1, t2) == (t, t) *)
    by move/eqP/pair_equal_spec => [-> ->].
  - (* (t1, t2) \in l *)
    by apply: H.
  (* 追加ここまで *)
Qed.

Lemma unifies_pairs_swap s t1 t2 l :
  unifies_pairs s ((t1, t2) :: l) ->
  unifies_pairs s ((t2, t1) :: l).
Proof.
  (* 追加ここから *)
  move=> H t1' t2'.
  rewrite in_cons => /orP [/eqP/pair_equal_spec [-> ->] | H'].
  - (* (t1', t2') == (t2, t1) *)
    rewrite /unifies.
    apply/eqP; rewrite eq_sym; apply/eqP.
    apply: H.
    rewrite in_cons.
    by apply/orP; left.
  - (* (t1', t2') \in l *)
    apply: H.
    rewrite in_cons.
    by apply/orP; right.
  (* 追加ここまで *)
Qed.

Lemma unify_subs_sound h v t l s : (* unify subs sound が最も重要な補題であるとのこと *)
  (forall s l, unify2 h l = Some s -> unifies_pairs s l) ->
  unify_subs (unify2 h) v t l = Some s ->
  unifies_pairs s ((Var v, t) :: l).
(*
  seq (tree * tree)型のリストl'にh回unify1を適用した結果、
  option (seq (var * tree))型のリストs'が得られて、
  任意のツリーt1',t2'について、タプル(t1',t2')が前記のリストl'に含まれるなら、
  得られたリストs'の元でt1'とt2'を等しくできるとする。
  そして、unify_subs (unify2 h) v t l の結果がsに等しいとする。
  すると、任意のツリーのタプル(t1,t2)がリスト(Var v, t) :: lに含まれるならsの元でt1とt2を等しくできる。
*)
Proof.
  rewrite /unify_subs.
  (*
    ゴールは
    (forall (s0 : seq (var * tree)) (l0 : seq (tree * tree)), unify2 h l0 = Some s0 -> unifies_pairs s0 l0) ->
    (if v \in vars t then None else may_cons v t (unify2 h [seq subs_pair v t i | i <- l])) = Some s ->
    unifies_pairs s ((Var v, t) :: l)
    となる。
  *)
  case Hocc: (v \in _) => // IH.
  (*
    (v \in vars t) = true or false で場合分け。
    (v \in vars t) = true の場合は try done で証明完了。
    (v \in vars t) = false の場合について
    まずフォーカスを IH という名前でコンテキストにポップ。
    ゴールは
    may_cons v t (unify2 h [seq subs_pair v t i | i <- l]) = Some s ->
    unifies_pairs s ((Var v, t) :: l)
    となる。
    (
      vars t は、t : tree に含まれる Var x の x の部分を集めたリストらしい。
      (v \in vars t) = false は、t : tree には Var v が含まれていないということ？
    )
  *)
  case Hun: (unify2 _ _) => [s'|] //= [] <-.
  (*
    (unify2 h [seq subs_pair v t i | i <- l]) = Some s' or None で場合分け。
    None の場合は try done で証明完了。
    Some s' の場合について
    Some ((v, t) :: s') = Some s から (v, t) :: s' = s を導いて
    ゴールの s を書き換えて、最終的にゴールは
    unifies_pairs ((v, t) :: s') ((Var v, t) :: l)
    となる。
    ゴールの意味は、
    forall t1 t2 : tree_eqType,
      (t1, t2) \in (Var v, t) :: l ->
      unifies ((v, t) :: s') t1 t2
    ↓
    任意のツリーt1,t2について、
    (t1,t2)がリスト(Var v,t)::lに含まれていれば、
    リスト(v,t)::s'の元でt1とt2を等しくすることができる。
    ということらしい。
    Check [seq subs_pair v t i | i <- l] : seq (tree * tree).
    となることより、
    Hun : unify2 h [seq subs_pair v t i | i <- l] = Some s'
    が意味するところは、
    seq (tree * tree)型のリストlから要素を1個ずつ取り出して、
    ツリーに含まれる変数vをツリーtで置き換えたseq (tree * tree)型のリストを求めて、
    求めたリストにh回関数unify1を適用した結果得られたoption (seq (var * tree))型のリストは
    Some s'であるということらしい。
  *)
  (* 追加ここから *)
  move: (Hocc) => /negbT/subs_same => Hocc'.
  move: (Hun).
  rewrite /subs_pair => Hun'.
  rewrite /unifies_pairs => t1 t2.
  rewrite in_cons => /orP.
  case.
  - (* (t1, t2) == (Var v, t) *)
    move/eqP.
    rewrite pair_equal_spec.
    case => [-> ->].
    rewrite /unifies /subs_list /= Hocc'.
    case Hvv : (v == v); first done.
    by rewrite eq_refl in Hvv.
  - (* (t1, t2) \in l *)
    move=> Ht1t2inl.
    rewrite /unifies /subs_list /=.
    apply: (IH s' [seq (subs v t p.1, subs v t p.2) | p <- l]); first done.
    move: (@map_f _ _ (fun p : (tree * tree) => (subs v t p.1, subs v t p.2)) l (t1, t2)).
    by apply.
  (* 追加ここまで *)
Qed.

(* unify2 の健全性*)
Theorem unify2_sound h s l :
  unify2 h l = Some s ->
  unifies_pairs s l.
(*
  リストlに対して関数unify1をh回適用した結果リストsが得られたなら、
  任意のツリーt1,t2について、
  (t1,t2)がlに含まれていればsの元でt1とt2を等しくすることができる。
*)
Proof.
  (*
    h : nat
    s : seq (var * tree)
    l : seq (tree * tree)
  *)
  elim: h s l => //= h IH s l.
  (*
    h に関する帰納法
    h = 0 の場合は try done により証明完了
    h > 0 の場合
    ゴールは
    unify1 (unify2 h) (size_pairs l + 1) l = Some s -> unifies_pairs s l
    となる
   *)
  move: (size_pairs l + 1) => h'.
  (*
    ゴールの (size_pairs l + 1) : nat を汎化してから
    コンテキストに h' : nat としてポップしている模様
  *)
  elim: h' l => //= h' IH' [] //.
  (*
    h' に関する帰納法
    h' = 0 の場合は try done により証明完了
    h' > 0 の場合
    l : seq (tree * tree) が空リストの場合と空リストでない場合とで場合分け
    空リストの場合は try done により証明完了
    l が空リストで無い場合、フォーカスの左辺は以下の様に場合分けされる模様
    (Var x, Var x0) :: r => if x == x0 then unify1 (unify2 h) h' r else unify_subs (unify2 h) x (Var x0) r
    (Var x, Sym _ as t0) :: r | (Var x, Fork _ _ as t0) :: r => unify_subs (unify2 h) x t0 r
    (Sym b as t, Var x) :: r => unify_subs (unify2 h) x t r
    (Sym b as t, Sym b') :: r => if is_left (symbol_dec b b') then unify1 (unify2 h) h' r else None
    (Sym b as t, Fork _ _) :: _ => None
    (Fork t1 t2 as t, Var x) :: r => unify_subs (unify2 h) x t r
    (Fork t1 t2 as t, Sym _) :: _ => None
    (Fork t1 t2 as t, Fork t1' t2') :: r => unify1 (unify2 h) h' [:: (t1, t1'), (t2, t2') & r]
  *)
  move=> [t1 t2] l.
  (* x, x0, r を t1, t2, l としてコンテキストにポップ *)
  destruct t1, t2 => //.
  (* t, t2 で場合分けし、自明の場合を try done で証明完了 *)
  (* VarVar *)
  - case: ifP.
      move/eqP => <- /IH'.
      by apply unifies_pairs_same.
    intros; by apply (unify_subs_sound h).
  (* VarSym *)
  - intros; by apply (unify_subs_sound h).
  (* 追加ここから *)
  (* VarFork *)
  - move=> H.
    apply: (unify_subs_sound h).
    move=> s0 l0.
    apply: IH.
    by apply: H.
  (* SymVar *)
  - move=> H.
    apply/unifies_pairs_swap/(unify_subs_sound h).
    move=> s1 l0.
    apply: IH.
    by apply: H.
  (* SymSym *)
  - case (symbol_dec s0 s1) => Hs0s1 //= H. (* s0 <> s1 の場合は try done により証明完了 *)
    rewrite Hs0s1.
    by apply/unifies_pairs_same/IH'/H.
  (* ForkVar *)
  - move=> H.
    apply/unifies_pairs_swap/(unify_subs_sound h).
    move=> s0 l0.
    apply: IH.
    by apply: H.
  (* ForkFork *)
  - move=> H.
    rewrite /unifies_pairs => t1 t2.
    rewrite in_cons => /orP [/eqP/pair_equal_spec [-> ->] | H'].
    + (* (t1, t2) == (Fork t1_1 t1_2, Fork t2_1 t2_2) *)
      rewrite /unifies.
      rewrite !subs_list_Fork.
      move: ((IH' [:: (t1_1, t2_1), (t1_2, t2_2) & l]) H) => H'.
      have -> : subs_list s t1_1 = subs_list s t2_1.
        apply: H'.
        rewrite in_cons.
        by apply/orP; left.
      have -> : subs_list s t1_2 = subs_list s t2_2.
        apply: H'.
        rewrite in_cons.
        apply/orP; right; rewrite in_cons.
        by apply/orP; left.
      by [].
    + (* (t1, t2) \in l *)
      apply: (IH' [:: (t1_1, t2_1), (t1_2, t2_2) & l]); first done.
      rewrite !in_cons.
      rewrite Bool.orb_assoc.
      apply/orP/orP/orP.
      by right.
  (* 追加ここまで *)
Qed.

(* 単一化の健全性*)
Corollary soundness t1 t2 s :
  unify t1 t2 = Some s ->
  unifies s t1 t2.
(*
  第1引数t1と第2引数t2に含まれる変数の数だけ、タプル(t1, t2)に関数unify2を再帰的に適用した結果、リストsが得られたなら、
  sの元でt1とt2を等しくすることができる。
  (「unify t1 t2」が t1, t2 に関する単一化を表していて、
   「unifies s t1 t2」が単一化を行った結果得られた s が t1, t2 の単一子であることを表している？
   単一化の結果、None でない何某かのリスト s が得られたら、それは単一子になっているということ？)
*)
Proof.
  (* 追加ここから *)
  move=> H.
  apply: (@unify2_sound (size (vars_pairs [:: (t1, t2)]) + 1) s [:: (t1, t2)]).
  - by rewrite /unify in H.
  - by rewrite mem_seq1.
  (* 追加ここまで *)
Qed.

(* 完全性*)

(* s が s' より一般的な単一子である*)
Definition moregen s s' :=
  exists s2,
    forall t,
      subs_list s' t = subs_list s2 (subs_list s t).
(*
  moregenは、
  任意の(変数とツリーのタプルの)リストs,s'について、
  ある(変数とツリーのタプルの)リストs2が存在して、
  任意のツリーtについて、
  sの元でtの変数を置き換えてできたツリーの変数をs2に従って置き換えると、
  s'のもとでtの変数を置き換えてできたツリーと等しくすることができる。
  という命題を表している模様。
*)

(* 自己確認ここから *)
Eval compute in unify (Fork (Sym "a") (Sym "b")) (Fork (Var 1) (Var 2)).
(* = Some [:: (1, Sym "a"); (2, Sym "b")] : option (seq (var * tree)) *)

Eval compute in subs_list [:: (1, Sym "a"); (2, Sym "b")] (Fork (Var 1) (Var 2)).
(* = Fork (Sym "a") (Sym "b") : tree *)

Eval compute in subs_list [:: (1, Sym "a"); (2, Sym "b"); (3, Sym "c")] (Fork (Var 1) (Var 2)).
(* = Fork (Sym "a") (Sym "b") : tree *)

Eval compute in subs_list [:: (1, Sym "a"); (2, Sym "b"); (3, Sym "c")] (Fork (Sym "a") (Sym "b")).
(* = Fork (Sym "a") (Sym "b") : tree *)

Goal
  unifies [:: (1, Sym "a"); (2, Sym "b"); (3, Sym "c")] (Fork (Sym "a") (Sym "b")) (Fork (Var 1) (Var 2)).
Proof.
  by [].
Qed.

Goal
  unify (Fork (Sym "a") (Sym "b")) (Fork (Var 1) (Var 2)) = Some [:: (1, Sym "a"); (2, Sym "b")].
Proof.
  by [].
Qed.

Eval compute in (vars (Fork (Sym "a") (Sym "b"))).
(* = [::] : seq var *)

Eval compute in (vars (Fork (Var 1) (Var 2))).
(* = [:: 1; 2] : seq var *)

Eval compute in (union (vars (Fork (Sym "a") (Sym "b"))) (vars (Fork (Var 1) (Var 2)))).
(* = [:: 1; 2] : seq var *)

Eval compute in [seq p <- [:: (1, Sym "a"); (2, Sym "b"); (3, Sym "c")]
                 | p.1 \in (union (vars (Fork (Sym "a") (Sym "b"))) (vars (Fork (Var 1) (Var 2))))].
(* = [:: (1, Sym "a"); (2, Sym "b")] : seq (nat_eqType * tree) *)

Goal
  unify (Fork (Sym "a") (Sym "b")) (Fork (Var 1) (Var 2))
  = Some [seq p <- [:: (1, Sym "a"); (2, Sym "b"); (3, Sym "c")]
          | p.1 \in (union (vars (Fork (Sym "a") (Sym "b"))) (vars (Fork (Var 1) (Var 2))))].
Proof.
  by [].
Qed.

Eval compute in [seq p <- [:: (1, Sym "a"); (2, Sym "b"); (3, Sym "c")]
                 | p.1 \notin (union (vars (Fork (Sym "a") (Sym "b"))) (vars (Fork (Var 1) (Var 2))))].
(* = [:: (3, Sym "c")] : seq (nat_eqType * tree) *)

Goal
  forall t,
    subs_list [:: (1, Sym "a"); (2, Sym "b"); (3, Sym "c")] t
    = subs_list [:: (3, Sym "c")] (subs_list [:: (1, Sym "a"); (2, Sym "b")] t).
Proof.
  by [].
Qed.
(* 自己確認ここまで *)

(* 単一化の完全性*)
Corollary unify_complete s t1 t2 :
  unifies s t1 t2 ->
  exists s1,
    unify t1 t2 = Some s1 /\ moregen s1 s.
(*
  sの元でt1とt2を等しいなら、
  s1が存在して、
  t1とt2に含まれる変数の数だけ(t1, t2)にunify2を再帰的に適用した結果得られたリストはs1に等しく、
  exists s2,
    forall t,
      subs_list s t = subs_list s2 (subs_list s1 t)
  が成り立つ。
  (リスト s がツリー t1, t2 の単一子であるなら、
   ツリー t1, t2 の単一化の結果、None でない何某かのリスト s1 が得られて、
   s1 に対応する s2 を選ぶことで、任意のツリー t について
   subs_list s t = subs_list s2 (subs_list s1 t)
   を成立させることができる、ということ？
   s が単一子であるならば、単一化により得られた s1 を元に、s1 に対応する s2 を選ぶことで、
   s と同じ働きをする単一子を構成することができるということ？
   単一子は、単一化により作り出すことができるということ？
   単一化により作り出した単一子が単一子の全てであり、単一化により作り出せない単一子は存在しないということ？)
*)
Proof.
  (* 追加ここから *)
  (*
    unify t1 t2 の結果得られる None でないリスト s1 には、
    t1, t2 に含まれる(全てとは限らない)変数と、
    その変数に対応する値(ツリー)のタプルが含まれるはず。
    そして、リスト s2 として、s1 に含まれない変数と対応する値(ツリー)のタプルからなるリストを選べば、
    任意のツリー t に対して s と同じ様に単一化を行えるはず。
    具体例での確認から、上記の様に予想して証明に着手。
  *)

  exists [seq p <- s | p.1 \in union (vars t1) (vars t2)].
  split.
  - rewrite /unify.
    rewrite addn1.
    rewrite /=.
    rewrite addn1.
    rewrite /=.
    admit. (* ここで手詰まり *)
  - rewrite /moregen.
    exists [seq p <- s | p.1 \notin union (vars t1) (vars t2)].
    elim s => //=.
    move=> a l IH t.
    admit. (* ここで手詰まり *)
  (* 証明完了に至っていない。補題 uniq_union の出番も見つかっていない。 *)

  (* 追加ここまで *)
Admitted.
