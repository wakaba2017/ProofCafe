From mathcomp Require Import all_ssreflect.

Section sort.

  Variable A : eqType.
  Variable le : A -> A -> bool.
  Variable le_trans: forall x y z, le x y -> le y z -> le x z.
  Variable le_total: forall x y, ~~ le x y -> le y x.

  Fixpoint insert a l := match l with
  | nil => (a :: nil)
  | b :: l' => if le a b then a :: l else b :: insert a l'
  end.

  Fixpoint isort l :=
  if l is a :: l' then insert a (isort l') else nil.

  Fixpoint sorted l := (* all を使ってbool 上の述語を定義する*)
  if l is a :: l' then all (le a) l' && sorted l' else true.

  Lemma le_seq_insert a b l :
    le a b ->
    all (le a) l ->
    all (le a) (insert b l).
  Proof.
    elim: l => /= [-> // | c l IH].
    move=> leab /andP [leac leal].
    case: ifPn => lebc /=.
    - by rewrite leab leac.
    - by rewrite leac IH.
  Qed.

  Lemma le_seq_trans a b l :
    le a b ->
    all (le b) l ->
    all (le a) l.
  Proof.
    move=> leab /allP lebl.
    apply/allP => x Hx.
    by apply/le_trans/lebl.
  Qed.

  Theorem insert_ok a l :
    sorted l ->
    sorted (insert a l).
  Proof.
    (* 追加ここから *)
    elim: l => //= a' l IH.
    move=> /andP [Hlea'l Hsl].
    case: ifPn => leaa' /=.
    - rewrite leaa' Hlea'l Hsl /= Bool.andb_true_r.
      by apply: (@le_seq_trans a a' l).
    - move: (IH Hsl) => ->.
      rewrite Bool.andb_true_r.
      move: leaa' => /le_total lea'a.
      by apply: le_seq_insert.
    (* 追加ここまで *)
  Qed.

  Theorem isort_ok l :
    sorted (isort l).
  Proof.
    (* 追加ここから *)
    elim: l => //= a l IH.
    by apply: insert_ok.
    (* 追加ここまで *)
  Qed.

  (* perm_eq がseq で定義されているが補題だけを使う*)
  Theorem insert_perm l a :
    perm_eq (a :: l) (insert a l).
  Proof.
    elim: l => //= b l pal.
    case: ifPn => //= leab.
    by rewrite (perm_catCA [:: a] [:: b]) perm_cons.
  Qed.

  (*
  perm_trans : forall (T : eqType), transitive (seq T) perm_eq
  *)

  Print perm_eq.
  (*
  perm_eq = 
  fun (T : eqType) (s1 s2 : seq T) =>
  all [pred x | count_mem x s1 == count_mem x s2] (s1 ++ s2)
       : forall T : eqType, seq T -> seq T -> bool
  *)
  Print count_mem.
  Print pred1.
  Print xpred1.

  Theorem isort_perm l :
    perm_eq l (isort l).
  Proof.
    (* 追加ここから *)
    elim: l => //= a l.
    rewrite -[perm_eq l _](@perm_cons _ a) => H.
    move: (insert_perm (isort l) a).
    by apply: (perm_trans H).
    (* 追加ここまで *)
  Qed.

End sort.

Check isort.

Definition isortn : seq nat -> seq nat := isort _ leq.
Definition sortedn := sorted _ leq.

Lemma leq_total a b :
  ~~ (a <= b) ->
  b <= a.
Proof.
  (* 追加ここから *)
  rewrite -ltnNge => Hblta.
  rewrite leq_eqVlt.
  apply/orP.
  by right.
  (* 追加ここまで *)
Qed.

Theorem isortn_ok l :
  sortedn (isortn l) && perm_eq l (isortn l).
Proof.
  (* 追加ここから *)
  apply/andP; split.
  - apply: isort_ok; last by apply: leq_total.
    move=> x y z.
    by apply: leq_trans.
  - by apply: isort_perm.
  (* 追加ここまで *)
Qed.

Require Import Extraction.
Extraction "isort.ml" isortn. (* コードが分かりにくい*)

Section even_odd.

  Notation even n := (~~ odd n). (* 単なる表記なので，展開が要らない*)

  Theorem even_double n :
    even (n + n).
  Proof.
    elim: n => // n.
    by rewrite addnS /= negbK.
  Qed.

  (* 等式を使ってn に対する通常の帰納法を可能にする*)
  Theorem even_plus m n :
    even m ->
    even n = even (m + n).
  Proof.
    elim: n => /= [|n IH] Hm.
    - by rewrite addn0.
    - by rewrite addnS IH.
  Qed.

  Theorem one_not_even :
    ~~ even 1.
  Proof.
    reflexivity.
  Qed.

  Theorem even_not_odd n :
    even n ->
    ~~ odd n.
  Proof.
    done.
  Qed.

  Theorem even_odd n :
    even n ->
    odd n.+1.
  Proof.
    (* 追加ここから *)
    by rewrite oddS.
    (* 追加ここまで *)
  Qed.

  Theorem odd_even n :
    odd n ->
    even n.+1.
  Proof.
    (* 追加ここから *)
    rewrite -addn1 oddD /=.
    by case: (odd n).
    (* 追加ここまで *)
  Qed.

  Theorem even_or_odd n :
    even n || odd n.
  Proof.
    (* 追加ここから *)
    elim: n => [| n].
    - by apply/orP; left.
    - move/orP => [Hnevn | Hnodd]; apply/orP.
      + by right.
      + by left; apply: odd_even.
    (* 追加ここまで *)
  Qed.

  Theorem odd_odd_even m n :
    odd m ->
    odd n = even (m + n).
  Proof.
    (* 追加ここから *)
    rewrite oddD => ->.
    by case: (odd n).
    (* 追加ここまで *)
  Qed.

End even_odd.
