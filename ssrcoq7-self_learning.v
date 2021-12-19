From mathcomp Require Import all_ssreflect.

Lemma exists_pred x :
  x > 0 ->
  exists y, x = S y.
Proof.
  case x => // n _. (* case: x と同じだが項が読みやすい*)
    by exists n.
Qed.
Print exists_pred.
(*
exists_pred = 
  fun x : nat =>
    match x as n return (0 < n -> exists y : nat, n = y.+1) with
    | 0 =>
        fun H : 0 < 0 =>
        let H0 : False := eq_ind (0 < 0) (fun e : bool => if e then False else True) I true H in
        False_ind (exists y : nat, 0 = y.+1) H0
    | n.+1 =>
        fun=> ex_intro (fun y : nat => n.+1 = y.+1) n (erefl n.+1)
    end
       : forall x : nat, 0 < x -> exists y : nat, x = y.+1
*)

Require Extraction.
Extraction exists_pred.                     (* 何も抽出されない*)

Print sig.
(*
Inductive sig (A : Type) (P : A -> Prop) : Type :=
  exist : forall x : A, P x -> {x : A | P x}
*)

Definition safe_pred x :
  x > 0 -> {y | x = S y}.
Proof.
  case x => // n _.        (* exists_pred と同じ*)
    by exists n. (* こちらもexists を使う*)
Defined.         (* 定義を透明にし，計算に使えるようにする*)

Require Extraction.
Extraction safe_pred.
(*
let safe_pred = function
                | O   -> assert false (* absurd case *)
                | S n -> n
*)
(* 自己確認
let safe_pred = fun x ->
                  match x with
                  | O   -> assert false (* absurd case *)
                  | S n -> n
と同じことらしい。
*)

Section Sort.

  Variables (A : Set) (le : A -> A -> bool).    (* データ型A とのその順序le *)
  (* 既に整列されたリストl の中にa を挿入する*)
  
  Fixpoint insert a (l : list A) :=
    match l with
    | nil     => (a :: nil)
    | b :: l' => if le a b
                 then a :: l            (* a が l の先頭要素以下なら l の先頭にコンスする *)
                 else b :: insert a l'  (* a が l の先頭要素より大なら l の残りに関数を再帰的に適用した結果に l の先頭要素をコンスする *)
    end.
  (* 自己確認ここから *)
  (*
    insert は、第1引数 a を、第2引数のリスト l に挿入する。
    挿入する位置は、値が a 以上の要素の直前となる。
  *)
  (* 自己確認ここまで *)
  
  (* 繰り返しの挿入でリストl を整列する*)
  Fixpoint isort (l : list A) : list A :=
    match l with
    | nil     => nil
    | a :: l' => insert a (isort l')
    end.
  (* 自己確認ここから *)
  (*
    isort は、引数のリスト l が
    空リストなら、何もしない。
    空リストでないなら、l の先頭要素 a を l の残りのリスト l' を isort したリストに
    insert を使って挿入する。
    (insertion sort というものか？)
  *)
  (* 自己確認ここまで *)
  
  (* le は推移律と完全性をみたす*)
  Hypothesis le_trans : (* 推移律 *)
    forall x y z,
      le x y ->
      le y z ->
      le x z.
  Hypothesis le_total : (* 完全性 *)
    forall x y,
      ~~ le x y ->
      le y x.
  
  (* le_list x l : x はあるリストl の全ての要素以下である*)
  Inductive le_list x : list A -> Prop :=
  | le_nil  : le_list x nil
  | le_cons : forall y l,
                le x y ->
                le_list x l ->
                le_list x (y::l).
  (* 自己確認ここから *)
  Check le_list
        : A -> seq A -> Prop.
  Check le_nil
        : forall x : A,
            le_list x [::].
  Check le_cons
        : forall (x y : A) (l : seq A),
            le x y ->
            le_list x l ->
            le_list x (y :: l).
  (* 自己確認ここまで *)
  
  (* sorted l : リストl は整列されている*)
  Inductive sorted : list A -> Prop :=
  | sorted_nil  : sorted nil
  | sorted_cons : forall a l,
                    le_list a l ->
                    sorted l ->
                    sorted (a::l).
  (* 自己確認ここから *)
  Check sorted
        : seq A -> Prop.
  Check sorted_nil
        : sorted [::].
  Check sorted_cons
        : forall (a : A) (l : seq A),
            le_list a l ->
            sorted l ->
            sorted (a :: l).
  (* 自己確認ここまで *)

  Hint Constructors le_list sorted.         (* auto の候補にする*)
  
  Lemma le_list_insert a b l :
    le a b ->
    le_list a l ->
    le_list a (insert b l).
  (*
    要素 a が要素 b 以下であり、
    要素 a がリスト l の全要素以下であるなら、
    要素 a は、リスト l に要素 b を insert してできたリストの全要素以下である。
  *)
  Proof.
    move=> leab.
    (* 自己確認ここから *)
    (*
    Check le_list_ind
          : forall (x : A) (P : seq A -> Prop),
              P [::] -> (* 前提1 *)
              (forall (y : A) (l : seq A), le x y -> le_list x l -> P l -> P (y :: l)) -> (* 前提2 *)
              forall l : seq A, le_list x l -> P l. (* 結論 *)
    Check insert : A -> seq A -> seq A.
    Check insert b : seq A -> seq A.
    Check insert b l : seq A.
    Check le_list : A -> seq A -> Prop.
    Check le_list a : seq A -> Prop.
    Check le_list a (insert b l) : Prop.
    Check (fun l => le_list a (insert b l)) : seq A -> Prop.
    Check le_list_ind a (fun l => le_list a (insert b l))
          : le_list a (insert b [::]) -> (* これが、le_list_ind の前提1に該当 *) (* ★1 *)
            (forall (y : A) (l : seq A),
               le a y ->
               le_list a l ->
               le_list a (insert b l) ->
               le_list a (insert b (y :: l))) -> (* これば、le_list_ind の前提2に該当 *) (* ★2 *)
            forall l : seq A,
              le_list a l ->
              le_list a (insert b l). (* これが、le_list_ind の結論に該当 *)
    apply: (le_list_ind a (fun l => le_list a (insert b l))).
    以下のelimは、上記のapplyと同じ意味
    *)
    (* 自己確認ここまで *)
    elim.
    - (* le_list_ind に渡した (fun l => le_list a (insert b l)) に空リストが渡された場合 *)
      rewrite /=.
      info_auto.
      (*
        (* info auto: *)
        simple apply le_cons (in core).
         assumption.
         simple apply le_nil (in core).
      *)
    - (* le_list_ind に渡した (fun l => le_list a (insert b l)) に空リストでないリストが渡された場合 *)
      move=> {l}. (* 詳細不明だが、コンテキストから l を削除しているように見える。 *)
      move=> c l.
      rewrite /=. (* これにより、ゴールの insert の定義が展開される模様(第2引数のリストは明らかに空リストではないことがわかる)。 *)
      Check ifPn
            : forall (A : Type) (b : bool) (vT vF : A),
                if_spec b vT vF (~~ b) b (if b then vT else vF).
      case: ifPn.
      + info_auto.
        (*
          (* info auto: *)
          intro.
          intro.
          intro.
          intro.
          simple apply le_cons (in core).
           assumption.
           simple apply le_cons (in core).
            assumption.
            assumption.
        *)
      + info_auto.
        (*
          (* info auto: *)
          intro.
          intro.
          intro.
          intro.
          simple apply le_cons (in core).
           assumption.
           assumption.
        *)
    Restart.
    move=> leab; elim => {l} [|c l] /=. info_auto.
    case: ifPn. info_auto. info_auto.
  Qed.

  Lemma le_list_trans a b l :
    le a b ->
    le_list b l ->
    le_list a l.
  Proof.
    move=> leab; elim. info_auto.
    info_eauto using le_trans.              (* 推移律はeauto が必要*)
  Qed.
  
  Hint Resolve le_list_insert le_list_trans. (* 補題も候補に加える*)

  Theorem insert_ok a l :
    sorted l ->
    sorted (insert a l).
  Proof.
    (* 追加ここから *)
    Check sorted_ind
          : forall P : seq A -> Prop,
              P [::] ->
              (forall (a : A) (l : seq A),
                 le_list a l ->
                 sorted l ->
                 P l ->
                 P (a :: l)) ->
              forall l : seq A,
                sorted l ->
                P l.
    Check (fun l => sorted (insert a l)) : seq A -> Prop.
    Check sorted_ind (fun l => sorted (insert a l))
          : sorted (insert a [::]) -> (* ★1 *)
            (forall (a0 : A) (l : seq A),
               le_list a0 l ->
               sorted l ->
               sorted (insert a l) ->
               sorted (insert a (a0 :: l))) -> (* ★2 *)
            forall l : seq A,
              sorted l ->
              sorted (insert a l).
    elim.
    - (* ★1の場合 *)
      rewrite /=.
      by apply: sorted_cons.
    - (* ★2の場合 *)
      move=> a' l'.
      rewrite /=.
      case: ifPn.
      + (* le a a' が true の場合 *)
        info_eauto using le_trans.
      + (* le a a' が false の場合 *)
        info_eauto using le_trans.
    Restart.
    elim => /= {l} [| h l]. by apply: sorted_cons.
    case: ifPn. info_eauto using le_trans. info_eauto using le_trans.
    (* 追加ここまで *)
  Qed.

  Hint Resolve insert_ok.

  Theorem isort_ok l :
    sorted (isort l).
  Proof.
    (* 追加ここから *)
    elim: l => //= a l IH.
    by apply: insert_ok.
    Restart.
    elim: l => //= a l IH.
    info_auto.
    (*
      (* info auto: *)
      simple apply insert_ok (in core).
       assumption.
    *)
    (* 追加ここまで *)
  Qed.

  Hint Resolve isort_ok.

  (* Permutation l1 l2 : リストl2 はl1 の置換である*)
  Inductive Permutation : list A -> list A -> Prop :=
  | perm_nil   : Permutation nil nil
  | perm_skip  : forall x l l',
                   Permutation l l' ->
                   Permutation (x::l) (x::l')
  | perm_swap  : forall x y l,
                   Permutation (y::x::l) (x::y::l)
  | perm_trans : forall l l' l'',
                   Permutation l l' ->
                   Permutation l' l'' ->
                   Permutation l l''.

  Hint Constructors Permutation.
  
  Theorem Permutation_refl l :
    Permutation l l.
  Proof.
    (* 追加ここから *)
    elim: l => //= a l IH.
    by apply: perm_skip.
    Restart.
    elim: l => //= a l IH.
    info_auto.
    (*
      (* info auto: *)
      simple apply perm_skip (in core).
       assumption.
    *)
    (* 追加ここまで *)
  Qed.

  Hint Resolve Permutation_refl.

  Theorem insert_perm l a :
    Permutation (a :: l) (insert a l).
  Proof.
    (* 追加ここから *)
    elim: l => /=; first apply: Permutation_refl.
    move=> a' l' IH.
    case: ifPn => Haa'; first apply: Permutation_refl.
    apply: (perm_trans [:: a, a' & l'] [:: a', a & l'] (a' :: insert a l')); first apply: perm_swap.
    by apply/perm_skip/IH.
    Restart.
    elim: l => //= a' l' IH.
    case: ifPn => Haa'.
    - info_auto.
    - info_eauto using perm_trans.
    (*
      (* info eauto: *)
      simple eapply perm_trans.
       simple apply Permutation_refl.
       simple eapply perm_trans.
        simple apply Permutation_refl.
        simple eapply perm_trans.
         simple apply perm_swap.
         simple apply perm_skip.
          exact IH.
    *)
    (* 追加ここまで *)
  Qed.

  Hint Resolve insert_perm.

  Theorem isort_perm l :
    Permutation l (isort l).
  Proof.
    (* 追加ここから *)
    elim: l => //= a l IH.
    apply: (perm_trans (a :: l) (a :: isort l) (insert a (isort l))); last apply: insert_perm.
    by apply/perm_skip/IH.
    Restart.
    elim: l => //= a l IH.
    info_eauto using perm_trans.
    (*
      (* info eauto: *)
      simple eapply perm_trans.
       simple apply Permutation_refl.
       simple eapply perm_trans.
        simple apply Permutation_refl.
        simple eapply perm_trans.
         simple apply perm_skip.
          exact IH.
          simple apply insert_perm.
    *)
    (* 追加ここまで *)
  Qed.
  
  (* 証明付き整列関数*)
  Definition safe_isort l :
    {l'|sorted l' /\ Permutation l l'}.
  Proof.
    exists (isort l).
    auto using isort_ok, isort_perm.
  Defined.

  Print safe_isort.

End Sort.

Check safe_isort.           (* le と必要な補題を与えなければならない*)

Extraction leq.             (* mathcomp のeqType の抽出が汚ない*)

Definition leq' m n :=
  if m - n is 0
  then true
  else false.

Extraction leq'.                            (* こちらはすっきりする*)
(*
let leq' m n =
  match subn m n with
  | O   -> True
  | S _ -> False
*)

Lemma leq'E m n :
  leq' m n = (m <= n).
Proof.
  rewrite /leq' /leq.
  by case: (m-n).
Qed.

Lemma leq'_trans m n p :
  leq' m n ->
  leq' n p ->
  leq' m p.
Proof.
  rewrite !leq'E; apply leq_trans.
Qed.

Lemma leq'_total m n :
  ~~ leq' m n ->
  leq' n m.
Proof.
  (* 追加ここから *)
  rewrite !leq'E -ltnNge [n <= m]leq_eqVlt => Hnltm.
  by apply/orP; right.
  (* 追加ここまで *)
Qed.

Definition isort_leq :=
  safe_isort nat leq' leq'_trans leq'_total.

Eval compute in proj1_sig (isort_leq (3 :: 1 :: 2 :: 0 :: nil)).
(* = [:: 0; 1; 2; 3] : seq nat *)

Extraction "isort.ml" isort_leq.

Section Sort'.

  Variables (A : Set) (le : A -> A -> bool).    (* データ型A とのその順序le *)

  Inductive All (P : A -> Prop) : list A -> Prop :=
  | All_nil  : All P nil
  | All_cons : forall y l,
                 P y ->
                 All P l ->
                 All P (y::l).

  (*
  ``All (le a) l`` が ``le list a l`` と同じ意味になる．
  こちらを使うように証明を修正せよ．
   *)
  
  (* 追加ここから *)
  Check All_nil
        : forall P : A -> Prop,
            All P [::].

  Check All_cons
        : forall (P : A -> Prop) (y : A) (l : seq A),
            P y ->
            All P l ->
            All P (y :: l).

  Hint Constructors All.

  Check le : A -> A -> bool.
  Check insert : forall A : Set, (A -> A -> bool) -> A -> seq A -> seq A.

  Lemma le_list_insert' a b l :
    le a b ->
    All (le a) l ->
    All (le a) (insert A le b l).
  Proof.
    Check All_ind
          : forall (P : A -> Prop) (P0 : seq A -> Prop),
              P0 [::] ->
              (forall (y : A) (l : seq A),
                 P y -> All P l -> P0 l -> P0 (y :: l)) ->
              forall l : seq A,
                All P l -> P0 l.
    Check (fun x : A => le a x) : A -> bool.
    Check (fun l : seq A => All (fun x : A => le a x) (insert A le b l)) : seq A -> Prop.
    Check (All_ind (fun x : A => le a x) (fun l : seq A => All (fun x : A => le a x) (insert A le b l)))
          : All (fun x : A => le a x) (insert A le b [::]) -> (* ★1 *)
            (forall (y : A) (l : seq A),
               le a y ->
               All (fun x : A => le a x) l ->
               All (fun x : A => le a x) (insert A le b l) ->
               All (fun x : A => le a x) (insert A le b (y :: l))) -> (* ★2 *)
            forall l : seq A,
              All (fun x : A => le a x) l ->
              All (fun x : A => le a x) (insert A le b l).
    move=> Hab.
    elim => /=.
    - (* ★1 *)
      by apply: All_cons.
    -  (* ★1 *)
      move=> y l0.
      case: ifPn.
      + (* le b y = true *)
        move=> Hby Hay H0 H1.
        apply: All_cons; first done.
        by apply: All_cons.
      + (* le b y = false *)
        move=> Hby Hay H0 H1.
        by apply: All_cons.
    Restart.
    move=> Hab.
    elim => /=.
    - (* ★1 *)
      info_auto.
    -  (* ★1 *)
      move=> y l0.
      case: ifPn.
      + (* le b y = true *)
        info_auto.
      + (* le b y = false *)
        info_auto.
  Qed.

  (* le は推移律と完全性をみたす*)
  Hypothesis le_trans : (* 推移律 *)
    forall x y z,
      le x y ->
      le y z ->
      le x z.
  Hypothesis le_total : (* 完全性 *)
    forall x y,
      ~~ le x y ->
      le y x.

  Lemma le_list_trans' a b l :
    le a b ->
    All (le b) l ->
    All (le a) l.
  Proof.
    move=> Hab.
    elim => //=.
    move=> y l0 Hby H0 H1.
    apply: All_cons; last done.
    by apply: (le_trans a b y).
    Restart.
    move=> Hab.
    elim.
    - info_auto.
    - info_eauto using le_trans.
  Qed.

  Inductive sorted' : list A -> Prop :=
  | sorted'_nil  : sorted' nil
  | sorted'_cons : forall a l,
                     All (le a) l ->
                     sorted' l ->
                     sorted' (a::l).

  Hint Constructors sorted'.

  Hint Resolve le_list_insert' le_list_trans'.

  Theorem insert_ok' a l :
    sorted' l ->
    sorted' (insert A le a l).
  Proof.
    elim => /=.
    - (* ★1の場合 *)
      by apply: sorted'_cons.
    - (* ★2の場合 *)
      move=> a' l' H0 H1 H2.
      case: ifPn => Haa'.
      + (* le a a' が true の場合 *)
        apply: sorted'_cons.
        * (* All (le a) (a' :: l') の証明 *)
          apply: All_cons; first done.
          by apply: (le_list_trans' a a' l').
        * (* sorted' (a' :: l') の証明 *)
          by apply: sorted'_cons.
      + (* le a a' が false の場合 *)
        apply: sorted'_cons; last done.
        apply: (le_list_insert' a' a l'); last done.
        by apply: (le_total a a').
    Restart.
    elim => /=.
    - (* ★1の場合 *)
      info_auto.
    - (* ★2の場合 *)
      move=> a' l'.
      case: ifPn.
      + (* le a a' が true の場合 *)
        info_eauto using le_trans.
      + (* le a a' が false の場合 *)
        info_eauto using le_trans.
  Qed.

  Hint Resolve insert_ok'.

  Theorem isort_ok' l :
    sorted' (isort A le l).
  Proof.
    elim: l => //= a l IH.
    by apply: insert_ok'.
    Restart.
    elim: l => //= a l IH.
    info_auto.
  Qed.

  (* Permutation の定義に変更は必要ない模様 *)

  Hint Constructors Permutation.

  Theorem Permutation_refl' l :
    Permutation A l l.
  Proof.
    elim: l => /=; first apply: perm_nil.
    move=> a l IH.
    by apply: perm_skip.
    Restart.
    elim: l => /=.
    - (* l が空リストの場合 *)
      info_auto.
    - (* l が空リストでない場合 *)
      info_auto.
  Qed.

  Hint Resolve Permutation_refl'.

  Theorem insert_perm' l a :
    Permutation A (a :: l) (insert A le a l).
  Proof.
    elim: l => /=; first apply: Permutation_refl'.
    move=> a' l' IH.
    case: ifPn => Haa'; first apply: Permutation_refl'.
    apply: (perm_trans A [:: a, a' & l'] [:: a', a & l'] (a' :: insert A le a l')); first apply: perm_swap.
    by apply/perm_skip/IH.
    Restart.
    elim: l => /=.
    - (* l が空リストの場合 *)
      info_auto.
    - (* l が空リストでない場合 *)
      move=> a' l' IH.
      case: ifPn => Haa'.
      + (* le a a' の場合 *)
        info_auto.
      + (* ~~ le a a' の場合 *)
        info_eauto using perm_trans.
  Qed.

  Hint Resolve insert_perm'.

  Theorem isort_perm' l :
    Permutation A l (isort A le l).
  Proof.
    elim: l => /=; first apply: perm_nil.
    move=> a l IH.
    apply: (perm_trans A (a :: l) (a :: isort A le l) (insert A le a (isort A le l))); last apply: insert_perm.
    by apply/perm_skip/IH.
    Restart.
    elim: l.
    - (* l が空リストの場合 *)
      info_auto.
    - (* l が空リストでない場合 *)
      info_eauto using perm_trans.
  Qed.
  (* 追加ここまで *)

End Sort'.

(* Hintにするしないで証明が変わってくる。
   できるだけHintを増やして、なるべくautoを使って証明する。 *)

(* END *)
