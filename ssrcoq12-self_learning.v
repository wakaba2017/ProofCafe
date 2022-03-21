From mathcomp Require Import all_ssreflect.

(* Lambda calculator *)

Module Lambda.

  Inductive expr : Set :=
    | Var of nat (* De Bruijn 添字*)
    | Abs of expr
    | App of expr & expr.

  Print expr.
  (*
    Inductive expr : Set :=
      Var : nat -> expr
    | Abs : expr -> expr
    | App : expr -> expr -> expr
  *)

  Fixpoint shift k (e : expr) := (* 自由変数をずらす*)
    match e with
    | Var n     => if k <= n
                   then Var n.+1
                   else Var n
    | Abs e1    => Abs (shift k.+1 e1)
    | App e1 e2 => App (shift k e1) (shift k e2)
  end.

(* 追加ここから *)
Eval compute in shift 0 (Var 1). (* = Var 2 : expr *) (* 0 <= 1 なので Var 1.+1 *)
Eval compute in shift 1 (Var 1). (* = Var 2 : expr *) (* 1 <= 1 なので Var 1.+1 *)
Eval compute in shift 2 (Var 1). (* = Var 1 : expr *) (* 2 >  1 なので Var 1    *)
Eval compute in shift 0 (Var 2). (* = Var 3 : expr *) (* 0 <= 2 なので Var 2.+1 *)
Eval compute in shift 1 (Var 2). (* = Var 3 : expr *) (* 1 <= 2 なので Var 2.+1 *)
Eval compute in shift 2 (Var 2). (* = Var 3 : expr *) (* 2 <= 2 なので Var 2.+1 *)
Eval compute in shift 3 (Var 2). (* = Var 2 : expr *) (* 2 >  2 なので Var 2    *)
(* 追加ここまで *)

  Fixpoint open_rec k u (e : expr) := (* 自由変数の代入*)
    match e with
    | Var n     => if k == n
                   then u
                   else
                     if leq k n
                     then Var n.-1
                     else e
    | Abs e1    => Abs (open_rec k.+1 (shift 0 u) e1)
    | App e1 e2 => App (open_rec k u e1) (open_rec k u e2)
  end.

  Inductive reduces : expr -> expr -> Prop := (* 簡約の導出規則*)
    | Rbeta : forall e1 e2,
                reduces (App (Abs e1) e2) (open_rec 0 e2 e1)
    | Rapp1 : forall e1 e2 e1',
                reduces e1 e1' ->
                reduces (App e1 e2) (App e1' e2)
    | Rapp2 : forall e1 e2 e2',
                reduces e2 e2' ->
                reduces (App e1 e2) (App e1 e2')
    | Rabs  : forall e1 e1',
                reduces e1 e1' ->
                reduces (Abs e1) (Abs e1').

  (* 簡約関係はreduces の反射推移閉包*)
  Inductive RT_closure {A} (R : A -> A -> Prop) : A -> A -> Prop :=
    | RTbase : forall a,
                 RT_closure R a a
    | RTnext : forall a b c,
                 R a b ->
                 RT_closure R b c ->
                 RT_closure R a c.

  Hint Constructors reduces RT_closure : core.

  Fixpoint reduce (e : expr) : option expr := (* 1 ステップ簡約*)
    match e with
    | App (Abs e1) e2 => Some (open_rec 0 e2 e1)
    | App e1 e2 =>
      match reduce e1, reduce e2 with
      | Some e1', _        => Some (App e1' e2)
      | None    , Some e2' => Some (App e1 e2')
      | None    , None     => None
      end
    | Abs e1 =>
      if reduce e1 is Some e1'
      then Some (Abs e1')
      else None
    | _ => None
    end.

  Fixpoint eval (n : nat) e := (* n ステップ簡約*)
    if n is k.+1 then
      if reduce e is Some e'
      then eval k e'
      else e
    else e.

  Coercion Var : nat >-> expr. (* 自然数を変数として直接に使える*)

  Definition church (n : nat) :=
    Abs (Abs (iter n (App 1) 0)). (* λf.λx.(fn x) *)

  Eval compute in church 3.
      (* = Abs (Abs (App 1 (App 1 (App 1 0)))) : expr *)
      (* 自己確認ここから
        = λf.λx.(f (f (f x)))
         自己確認ここまで *)

  Definition chadd := Abs (Abs (Abs (Abs (App (App 3 1) (App (App 2 1) 0))))).
                                                 (* λm.λn.λf.λx.(m f (n f x)) *)

  Eval compute in eval 6 (App (App chadd (church 3)) (church 2)).
      (* = Abs (Abs (App 1 (App 1 (App 1 (App 1 (App 1 0)))))) : expr *)
      (* 自己確認ここから
        = λf.λy.(f (f (f (f (f x)))))
         自己確認ここまで *)

  (* 自己確認ここから *)
  Eval compute in eval 0 (App (App chadd (church 3)) (church 2)).
  (*
     = App
         (App ・・・ 次にこの関数適用が評価される("Var 3"が置き換えられる)模様
            (Abs (Abs (Abs (Abs (App (App 3 1) (App (App 2 1) 0)))))) ・・・ chadd
            (Abs (Abs (App 1 (App 1 (App 1 0))))) ・・・ church 3
         )
         (Abs (Abs (App 1 (App 1 0)))) ・・・ church 2
     : expr
  *)
  Eval compute in eval 1 (App (App chadd (church 3)) (church 2)).
  (*
     = App ・・・ 次にこの関数適用が評価される("Var 2"が置き換えられる)模様
         (Abs (Abs (Abs (App (App "(Abs (Abs (App 1 (App 1 (App 1 0))))") 1) (App (App 2 1) 0)))))
          ・・・ chadd (church 3)
         (Abs (Abs (App 1 (App 1 0)))) ・・・ church 2
     : expr
  *)
  Eval compute in eval 2 (App (App chadd (church 3)) (church 2)).
  (*
     = Abs
         (Abs
            (App
               (App ・・・ 次にこの関数適用が評価される("Var 1"が置き換えられる)模様
                  "(Abs (Abs (App 1 (App 1 (App 1 0)))))"
                  1
               )
               (App (App "(Abs (Abs (App 1 (App 1 0))))" 1) 0)
            )
         )
     : expr
  *)
  Eval compute in eval 3 (App (App chadd (church 3)) (church 2)).
  (*
     = Abs
         (Abs
            (App ・・・ 次にこの関数適用が評価される("Var 2"と"Var 0"が置き換えられる)模様
               (Abs (App 2 (App 2 (App 2 0))))
               (App (App (Abs (Abs (App 1 (App 1 0)))) 1) 0)
            )
         )
     : expr
  *)
  Eval compute in eval 4 (App (App chadd (church 3)) (church 2)).
  (*
     = Abs
         (Abs
            (App 1 (App 1 (App 1
                               (App (App (Abs (Abs (App 1 (App 1 0)))) 1) 0)
                          )
                   )
            )
         )
     : expr
  *)
  Eval compute in eval 5 (App (App chadd (church 3)) (church 2)).
  (*
     = Abs
         (Abs
            (App 1 (App 1 (App 1
                               (App ・・・ 次にこの関数適用が評価される("Var 2"が置き換えられる)模様
                                  (Abs (App 2 (App 2 0)))
                                  0
                               )
                          )
                   )
            )
         )
     : expr
  *)
  Eval compute in eval 6 (App (App chadd (church 3)) (church 2)).
  (*
     = Abs (Abs (App 1 (App 1 (App 1 (App 1 (App 1 0))))))
     : expr
  *)
  (* 自己確認ここまで *)

  Lemma reduce_ok e e' : (* 1-step 簡約の健全性*)
    reduce e = Some e' ->
    reduces e e'.
  Proof.
    move: e'; induction e => //= e'.
      case He: (reduce e) => [e1|] // [] <-. (** e = Abs **)
      (* 書換えここから *)
      by apply/Rabs/IHe/He.
      (* 書換えここまで *)
    destruct e1 => //. (** e = App **)
    - (* 書換えここから *)
      (** e1 = Var **)
      rewrite /=.
      (* 横着せずに外側の match の場合分けをするには、以下の行に差し替えればよさそう。
      case Hn: (reduce n). case => <-. by apply/Rapp1/IHe1/Hn.
      *)
      case He2: (reduce e2); last done.
      case => <-.
      by apply/Rapp2/IHe2/He2.
      (* 書換えここまで *)
    - case => <-. (** e1 = Abs **)
      by constructor.
    - case He1: (reduce (App _ _)) => [e1'|]. (** e1 = App **)
        case => <-.
      (* 追加ここから *)
        by apply/Rapp1/IHe1/He1.
      case He2: (reduce e2); last done.
      case=> <-.
      by apply/Rapp2/IHe2/He2.
      (* 追加ここまで *)
  Qed.

  Theorem eval_ok n e e' : (* n-step 簡約の健全性*)
    eval n e = e' ->
    RT_closure reduces e e'.
  Proof.
    (* 追加ここから *)
    (* 追加ここまで *)
  Admitted.

  Fixpoint closed_expr n e := (* 変数がn 個以下の項*)
    match e with
    | Var k => k < n
    | App e1 e2 => closed_expr n e1 && closed_expr n e2
    | Abs e1 => closed_expr n.+1 e1
    end.

  Lemma shift_closed n e :
    closed_expr n e -> shift n e = e.
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq13.pdf を自習したときに作成した証明 *)
    elim: e n.
    - (* Var *)
      move=> n n0 IH /=.
      case: ifP; last done.
      (* (n0 <= n) = false の場合は、 last done により証明完了。 *)
      (* (n0 <= n) = true *)
        rewrite leqNgt => /negP H.
        by rewrite /= in IH.
    - (* Abs *)
      move=> e IHe n Hcl /=.
      rewrite IHe; first done.
      by rewrite /= in Hcl.
    - (* App *)
      move=> e IHe e0 IHe0 n Hcl /=.
      rewrite /= in Hcl.
      move: Hcl; move/andP; case => [Hcle Hcle0].
      rewrite IHe; last done.
      by rewrite IHe0; last done.
    (* 追加ここまで *)
  Qed.

  Lemma open_rec_closed n u e : (* n + 1 個目の変数を代入しても変わらない*) (* どこでで使う？ *)
    closed_expr n e ->
    open_rec n u e = e.
  Proof.
    move: n u.
    induction e => //= k u Hc.
    - case: ifP => Hk1.
        by rewrite (eqP Hk1) ltnn in Hc.
      by rewrite leqNgt Hc.
    (* 追加ここから *)
    - by rewrite IHe.
    - move: Hc => /andP [He1 He2].
      rewrite IHe1; last done.
      by rewrite IHe2; last done.
    (* 追加ここまで *)
  Qed.

  Lemma closed_iter_app n k e1 e2 : (* どこでで使う？ *)
    closed_expr k e1 -> closed_expr k e2 -> closed_expr k (iter n (App e1) e2).
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq13.pdf を自習したときに作成した証明 *)
    elim: n k e1 e2.
    - (* n = 0 の場合 *)
      move=> k e1 e2 Hclke1 Hclke2 /=.
      by apply: Hclke2.
    - (* n > 0 の場合 *)
      move=> n IHn k e1 e2 Hclke1 Hclke2.
      rewrite iterSr.
      apply: IHn => /=; first done.
      by apply/andP; split.
    (* 追加ここまで *)
  Qed.

  Lemma closed_church n : (* どこでで使う？ *)
    closed_expr 0 (church n).
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq13.pdf を自習したときに作成した証明 *)
    by elim: n.
    (* 追加ここまで *)
  Qed.

  Lemma closed_expr_S n e : (* どこでで使う？ *)
    closed_expr n e ->
    closed_expr n.+1 e.
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq13.pdf を自習したときに作成した証明 *)
    elim: e n.
    - (* コンストラクタが Var の場合 *)
      move=> n n0 /= H.
      rewrite ltnS leq_eqVlt.
      by apply/orP; right.
    - (* コンストラクタが Abs の場合 *)
      move=> e IHe n /= Hcln.
      by apply/IHe/Hcln.
    - (* コンストラクタが App の場合 *)
      move=> e IHe e0 IHe0 n /=.
      move/andP; case => [Hclne Hclne0].
      apply/andP; split.
      + (* closed_expr n.+1 e の証明 *)
        by apply/IHe/Hclne. 
      + (* closed_expr n.+1 e0 の証明 *)
        by apply/IHe0/Hclne0.
    (* 追加ここまで *)
  Qed.

  Hint Resolve closed_iter_app closed_church closed_expr_S.

  Lemma open_iter_app k n u e1 e2 :
    open_rec k u (iter n (App e1) e2) =
      iter n (App (open_rec k u e1)) (open_rec k u e2).
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq13.pdf を自習したときに作成した証明 *)
    elim: n k u e1 e2 => [// | n IHn k u e1 e2].
    (* n = 0 の場合は、 // により証明完了。 *)
    (* n > 0 の場合 *)
      rewrite 2!iterSr IHn.
      by f_equal.
    (* 追加ここまで *)
  Qed.

  Lemma reduces_iter n e1 e2 e2' : (* どこで使う？ *)
    reduces e2 e2' ->
    reduces (iter n (App e1) e2) (iter n (App e1) e2').
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq13.pdf を自習したときに作成した証明 *)
    elim: n e1 e2 e2' => [// | n IHn e1 e2 e2' H].
    (* n = 0 の場合は、 // により証明完了。 *)
    (* n > 0 の場合 *)
      rewrite 2!iterSr.
      by apply/IHn/Rapp2.
    (* 追加ここまで *)
  Qed.

  Eval compute in
    eval 1
      (App
         (Abs (Abs (Abs (App (App (Abs (Abs (iter 3 (App 1) 0))) 1) (App (App 2 1) 0)))))
         (church 2)
      ).
  (*
     = Abs
         (Abs
            (App (App (Abs (Abs "(App 1 (App 1 (App 1 0)))")) 1)
                 (App (App "(Abs (Abs (App 1 (App 1 0))))" 1) 0)
            )
         )
     : expr
  *)
  Eval compute in
    eval 2
      (App
         (Abs (Abs (Abs (App (App (Abs (Abs (iter 3 (App 1) 0))) 1) (App (App 2 1) 0)))))
         (church 2)
      ).
  (*
     = Abs
         (Abs
            (App
               (Abs (App 2 (App 2 (App 2 0))))
               (App (App (Abs (Abs (App 1 (App 1 0)))) 1) 0)
            )
         )
     : expr
  *)
  Eval compute in
    eval 3
      (App
         (Abs (Abs (Abs (App (App (Abs (Abs (iter 3 (App 1) 0))) 1) (App (App 2 1) 0)))))
         (church 2)
      ).
  (*
     = Abs
         (Abs
            (App 1 (App 1 (App 1 (App
                                    (App
                                       (Abs (Abs (App 1 (App 1 0))))
                                       1
                                    )
                                    0
                                 )
                          )
                   )
            )
         )
     : expr
  *)
  Eval compute in
    eval 4
      (App
         (Abs (Abs (Abs (App (App (Abs (Abs (iter 3 (App 1) 0))) 1) (App (App 2 1) 0)))))
         (church 2)
      ).
  (*
     = Abs (Abs (App 1 (App 1 (App 1 (App
                                        (Abs (App 2 (App 2 0)))
                                        0
                                     )
                              )
                       )
                )
           )
     : expr
  *)
  Eval compute in
    eval 5
      (App
         (Abs (Abs (Abs (App (App (Abs (Abs (iter 3 (App 1) 0))) 1) (App (App 2 1) 0)))))
         (church 2)
      ).
  (*
     = Abs (Abs (App 1 (App 1 (App 1 (App 1 (App 1 0))))))
     : expr
  *)

Eval compute in
  eval 1
  (Abs
     (Abs
        (App
           (App (Abs (Abs (iter 3 (App 1) 0))) 1)
           (App (App (Abs (Abs (iter 2 (App 1) 0))) 1) 0)
        )
     )
  ).
(*
     = Abs
         (Abs
            (App
               (Abs (iter 3 (App 2) 0))
               (App (App (Abs (Abs (iter 2 (App 1) 0))) 1) 0)
            )
         )
     : expr

     = Abs
         (Abs
            (App
               (Abs "(App 2 (App 2 (App 2 0)))")
               (App (App (Abs (Abs "(App 1 (App 1 0))")) 1) 0)
            )
         )
     : expr
*)

Eval compute in
  eval 1
  (Abs
     (Abs
        (App (* この関数適用が評価される模様 *)
           (Abs
              (iter 3 (App 2) 0)
           )
           (App (App (Abs (Abs (iter 2 (App 1) 0))) 1) 0)
        )
     )
  ).
(*
     = Abs
         (Abs
            (App 1 (App 1 (App 1
                               (App (App (Abs (Abs "(App 1 (App 1 0))")) 1) 0)
                          )
                   )
            )
         )
     : expr
*)

  Theorem chadd_ok' m n : (* Church 数の足し算が正しい*)
    RT_closure reduces (App (App chadd (church m)) (church n)) (church (m + n)).
  Proof.
    eapply RTnext; repeat constructor.
    rewrite /= !shift_closed; auto.
    (* 追加ここから *)
    (* 追加ここまで *)
  Admitted.

(*
  (App
     (Abs
        (Abs
           (Abs
              (App
                 (App
                    (Abs
                       (Abs
                          (iter m (App 1) 0)
                       )
                    )
                    1
                 )
                 (App
                    (App 2 1)
                    0
                 )
              )
           )
        )
     )
     (church n)
  )

  (App
     (λn'.
        (λf'.
           (λx'.
              (App
                 (App
                    (λf.
                       (λx.
                          (iter m (App f) x)
                       )
                    )
                    f'
                 )
                 (App
                    (App n' f')
                    x'
                 )
              )
           )
        )
     )
     (church n)
  )

  (λf'.
     (λx'.
        (App
           (App
              (λf.
                 (λx.
                    (iter m (App f) x)
                 )
              )
              f'
           )
           (App
              (App (church n) f')
              x'
           )
        )
     )
  )

  (λf'.
     (λx'.
        (App
           (App λf.λx.(iter m (App f) x) f')
           (App (App (church n) f') x')
        )
     )
  )

  (λf'.
     (λx'.
        (App
           λx.(iter m (App f') x)
           (App (App (church n) f') x')
        )
     )
  )

  λf'.λx'.(iter m (App f') (App (App (church n) f') x'))

  λf'.λx'.(iter m (App f') (App (App (Abs (Abs (iter n (App 1) 0))) f') x'))

  λf'.λx'.(iter m (App f') (App (App λf''.λx''.(iter n (App f'') x'') f') x'))

  λf'.λx'.(iter m (App f') (App λx''.(iter n (App f') x'') x'))

  λf'.λx'.(iter m (App f') (iter n (App f') x'))

  (Abs (Abs (iter m (App 1) (iter n (App 1) 0))))

*)

  Lemma eval_add m n e :
    eval (m + n) e = eval m (eval n e).
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq13.pdf を自習したときに作成した証明 *)
    elim: n m e => [| n IHn] m e.
    - (* n = 0 の場合 *)
      by rewrite /= addn0.
    - (* n > 0 の場合 *)
      rewrite -[in LHS]addn1 addnA addn1 /=.
      case_eq (reduce e) => [a |].
      + (* reduce e = Some a の場合 *)
        by rewrite IHn.
      + (* reduce e = None の場合 *)
        case: m => [// | m'].
        (* m = 0 の場合は、 // により証明完了。 *)
        (* m > 0 の場合 *)
          by move=> /= ->.
    (* 追加ここまで *)
  Qed.

  Lemma reduce_iter_app n (k : nat) x :
    reduce (iter n (App k) x) =
      if reduce x is Some x' then Some (iter n (App k) x') else None.
  Proof.
    (* 追加ここから *)
    (* 以下は、2017年度の coq13.pdf を自習したときに作成した証明 *)
    elim: n k x.
    - (* n = 0 の場合 *)
      move=> k x /=.
      by case: (reduce x).
    - (* n > 0 の場合 *)
      move=> n IHn k x.
      rewrite iterSr IHn /=.
      case: (reduce x) => [a | //].
      (* reduce x = None の場合は、 // により証明完了。 *)
      (* reduce x = Some x' の場合 *)
        by rewrite -iterSr iterS.
    (* 追加ここまで *)
  Qed.

  Theorem chadd_ok m n : (* reduce でも証明(帰結ではない) *)
    exists h, exists h',
      eval h (App (App chadd (church m)) (church n)) = eval h' (church (m+n)).
  Proof.
    elim: m n => [|m IHm] n.
      rewrite add0n.
      exists 6; exists 0 => /=.
      rewrite !shift_closed; auto.
      by rewrite !open_iter_app /=.
    move: {IHm}(IHm n.+1) => [h [h' IHm]].
    exists (6+h); exists (6+h').
    rewrite (addSnnS m) -(addn1 m).
    move: (f_equal (eval 6) IHm).
    rewrite -!eval_add => <- /=.
    rewrite !shift_closed /=; auto.
    rewrite !open_iter_app /=.
    do! rewrite !reduce_iter_app /=.
    by rewrite iter_add.
  Qed.

End Lambda.
