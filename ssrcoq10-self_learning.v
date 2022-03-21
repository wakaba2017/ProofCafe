From mathcomp Require Import all_ssreflect all_algebra. (* 代数ライブラリ *)

Local Open Scope ring_scope. (* 環構造を使う *)
Import GRing.Theory.

Section Problem1.

  Variable K : fieldType. (* 体 *)
  Variable E : vectType K. (* 有限次元ベクトル空間 *)
  Variable f : 'End(E). (* 線形変換 *)

  Print limg. (* Notation limg f := (f @: fullv)%VS *)
  Check @lker
        : forall (K : fieldType) (aT rT : vectType K),
            'Hom(aT, rT) ->
            {vspace aT}.
  Locate "\o".
  (*
    Notation "f1 \o f2" := (comp f1 f2) : fun_scope (default interpretation)
    Notation "f \o g" := (comp_lfun f g) : lfun_scope  ※ここでは、こちらの意味らしい。
  *)
  Check comp_lfun
        : forall (R : ringType) (aT vT rT : vectType R),
            'Hom(vT, rT) ->
            'Hom(aT, vT) ->
            'Hom(aT, rT).
  Locate "@:".
  (*
    Notation "f @: A" := (Imset.imset f (mem A)) : set_scope
      (default interpretation)
    Notation "f @: U" := (lfun_img f U) : vspace_scope  ※ここでは、こちらの意味らしい。
  *)
  Check @lfun_img
        : forall (K : fieldType) (aT rT : vectType K),
            'Hom(aT, rT) ->
            {vspace aT} ->
            {vspace rT}.

  Theorem equiv1 :
    (limg f + lker f)%VS = fullv <-> limg f = limg (f \o f).
    (*
      E を K 上のベクトル空間とすると、
        E = Im f ⊕ Ker f
      と
        Im f = im (f ⚪ f)
      は同値である。
    *)
  Proof.
    split.
    - (* (limg f + lker f)%VS = fullv -> limg f = limg (f \o f) の証明 *)

      Check f_equal
            : forall (A B : Type) (f : A -> B) (x y : A),
                x = y ->
                f x = f y.

      Check @lfun_img
            : forall (K : fieldType) (aT rT : vectType K),
                'Hom(aT, rT) ->
                {vspace aT} ->
                {vspace rT}.

      Check @lfun_img _ _ _ f : {vspace E} -> {vspace E}.

      Check lfun_img f : {vspace E} -> {vspace E}.

      Check f_equal (lfun_img f)
            : forall x y : {vspace E},
                x = y ->
                (f @: x)%VS = (f @: y)%VS.

      move/(f_equal (lfun_img f)).
      rewrite limg_comp limgD.
      (* 追加ここから *)
      move=> H; rewrite -[LHS]H.
      have -> : (f @: lker f)%VS = 0%VS.
        apply/eqP.
        rewrite -(lkerE f (lker f)).
        by apply: subvv.
      by rewrite addv0.
      (* 追加ここまで *)
    - (* limg f = limg (f \o f) -> (limg f + lker f)%VS = fullv の証明 *)
      rewrite limg_comp => Hf'.
      (*
        limg f = limg (f \o f) -> (limg f + lker f)%VS = fullv
        ↓
        ↓rewrite limg_comp.
        ↓
        limg f = (f @: limg f)%VS -> (limg f + lker f)%VS = fullv
        ↓
        ↓move=> Hf'.
        ↓
        (limg f + lker f)%VS = fullv
      *)
      move: (limg_ker_dim f (limg f)).
      (*
        (limg f + lker f)%VS = fullv
        ↓
        ↓move: (limg_ker_dim f (limg f)).
        ↓
        (\dim (limg f :&: lker f) + \dim (f @: limg f))%N = \dim (limg f) ->
        (limg f + lker f)%VS = fullv
      *)
      rewrite -[RHS]add0n -Hf' => /eqP.
      (*
        (\dim (limg f :&: lker f) + \dim (f @: limg f))%N = \dim (limg f) ->
        (limg f + lker f)%VS = fullv
        ↓
        ↓rewrite -[RHS]add0n.
        ↓
        (\dim (limg f :&: lker f) + \dim (f @: limg f))%N = (0 + \dim (limg f))%N ->
        (limg f + lker f)%VS = fullv
        ↓
        ↓rewrite -Hf'.
        ↓
        (\dim (limg f :&: lker f) + \dim (limg f))%N = (0 + \dim (limg f))%N ->
        (limg f + lker f)%VS = fullv
        ↓
        ↓move/eqP.
        ↓
        (\dim (limg f :&: lker f) + \dim (limg f))%N == (0 + \dim (limg f))%N ->
        (limg f + lker f)%VS = fullv
      *)
      rewrite eqn_add2r dimv_eq0 => /eqP /dimv_disjoint_sum.
      (*
        (\dim (limg f :&: lker f) + \dim (limg f))%N == (0 + \dim (limg f))%N ->
        (limg f + lker f)%VS = fullv
        ↓
        ↓rewrite eqn_add2r.
        ↓
        \dim (limg f :&: lker f) == 0 -> (limg f + lker f)%VS = fullv
        ↓
        ↓rewrite dimv_eq0.
        ↓
        (limg f :&: lker f)%VS == 0%VS -> (limg f + lker f)%VS = fullv
        ↓
        ↓move/eqP.
        ↓
        (limg f :&: lker f)%VS = 0%VS -> (limg f + lker f)%VS = fullv
        ↓
        ↓move/dimv_disjoint_sum.
        ↓
        \dim (limg f + lker f) = (\dim (limg f) + \dim (lker f))%N ->
        (limg f + lker f)%VS = fullv
      *)
      (* 追加ここから *)
      (* 追加ここまで *)
  Admitted.

End Problem1.

Section Problem2.

  Variable K : numFieldType.  (* ノルム付き体 *)
  Variable E : vectType K.
  Variable p q : 'End(E).

  Definition projection (f : 'End(E)) := forall x, f (f x) = f x.

  Lemma proj_idE f :
    projection f <-> {in limg f, f =1 id}.
  Proof.
  split => Hf x.
  - by move/limg_lfunVK => <-.
  - by rewrite Hf // memv_img ?memvf.
  Qed.

  Hypothesis proj_p : projection p.
  Hypothesis proj_q : projection q.

  Section a.

    Lemma f_g_0 f g x :
      projection f ->
      projection g ->
      projection (f + g) ->
      f (g x) = 0.
    Proof.
      move=> Pf Pg /(_ (g x)).
      (*
        move=> Pf Pg => H. move: (H (g x)).
        projection (f + g) をフォーカスに残して、
        汎化されている変数を(g x)に特殊化している模様。
      *)
      Check add_lfunE
            : forall (R : ringType) (aT rT : vectType R) (f g : 'Hom(aT, rT)) (x : aT),
                (f + g) x = f x + g x.
      Check linearD
            : forall (R : ringType) (U : lmodType R) (V : zmodType) 
                     (s : R -> V -> V) (f : {linear U -> V | s}), {morph f : x y / 
                x + y >-> x + y}.
      rewrite !add_lfunE !linearD /=.
      (*
        (f + g) ((f + g) (g x)) = (f + g) (g x) ->
        f (g x) = 0
        ↓
        ↓rewrite !add_lfunE.
        ↓
        f (f (g x) + g (g x)) + g (f (g x) + g (g x)) = f (g x) + g (g x) ->
        f (g x) = 0
        ↓
        ↓rewrite !linearD.
        ↓
        lfun_linear f (f (g x)) + lfun_linear f (g (g x)) +
       (lfun_linear g (f (g x)) + lfun_linear g (g (g x))) = f (g x) + g (g x) ->
        f (g x) = 0
        ↓
        ↓rewrite /=.
        ↓
        f (f (g x)) + f (g (g x)) + (g (f (g x)) + g (g (g x))) = f (g x) + g (g x) -> f (g x) = 0
      *)
      rewrite !Pf !Pg => /eqP.
      (*
        f (f _) → f _
        g (g _) → g _
      *)
      rewrite -subr_eq !addrA addrK.
      rewrite addrAC eq_sym -subr_eq eq_sym subrr => /eqP Hfg.
      move: (f_equal g Hfg).
      rewrite !linearD /= Pg linear0 => /eqP.
      (* 追加ここから *)
      rewrite addr_eq0 => /eqP Hgfg.
      move: (Hfg); rewrite Hgfg => Hfg'.
      move: (Hfg') => /eqP; rewrite subr_eq0 => /eqP Hfg''.
      move: (Hfg); rewrite -Hfg'' => /eqP.
      rewrite -mulr2n -scaler_nat scaler_eq0 => /orP [H2eq0 | Hfgxeq0].
      - by rewrite Num.Theory.pnatr_eq0 in H2eq0.
      - by apply/eqP.
      (* 追加ここまで *)
    Qed.

    Theorem equiv2 :
      projection (p + q) <-> (forall x, p (q x) = 0 /\ q (p x) = 0).
      (*
        p ⚪ q = q ⚪ p = 0 が p + q が射影写像であることの必要十分条件である。
      *)
    Proof.
      split=> H x.
      (* 追加ここから *)
      - split.
        + by apply: (f_g_0 p q x).
        + apply: (f_g_0 q p x) => //=.
          by rewrite addrC.
      - rewrite !add_lfunE !linearD /=.
        rewrite !proj_p !proj_q.
        move: (H x).
        case => [-> ->].
        by rewrite addr0 addrA addr0.
      (* 追加ここまで *)
    Qed.

  End a.

  Section b.

    Hypothesis proj_pq : projection (p + q).

    Lemma b1a x :
      x \in limg p ->
      x \in limg q ->
      x = 0.
    Proof.
      (* 追加ここから *)
      (* 追加ここまで *)
    Admitted.

    Lemma b1b :
      directv (limg p + limg q).
    Proof.
      apply/directv_addP/eqP.
      (*
        directv (limg p + limg q).
        ↓
        ↓apply/directv_addP/eqP.
        ↓
        (limg p :&: limg q)%VS == 0%VS
      *)
      rewrite -subv0.
      (*
        (limg p :&: limg q)%VS == 0%VS
        ↓
        ↓rewrite -subv0.
        ↓
        (limg p :&: limg q <= 0)%VS
      *)
      apply/subvP => u /memv_capP [Hp Hq].
      (*
        (limg p :&: limg q <= 0)%VS
        ↓
        ↓apply/subvP.
        ↓
        {subset (limg p :&: limg q)%VS <= 0%VS}
        ↓
        ↓move=> u.
        ↓
        u \in (limg p :&: limg q)%VS -> u \in 0%VS
        ↓
        ↓move/memv_capP.
        ↓
        u \in limg p /\ u \in limg q -> u \in 0%VS
        ↓
        ↓case => [Hp Hq].
        ↓
        u \in 0%VS
      *)
      rewrite memv0.
      (*
        u \in 0%VS
        ↓
        ↓rewrite memv0.
        ↓
        u == 0
      *)
      (* 追加ここから *)
      by apply/eqP/b1a.
      (* 追加ここまで *)
    Qed.

    Lemma limg_sub_lker f g :
      projection f ->
      projection g ->
      projection (f + g) ->
      (limg f <= lker g)%VS.
    Proof.
      (* 追加ここから *)
      (* 追加ここまで *)
    Admitted.

    Lemma b1c :
      (limg p <= lker q)%VS.
    Proof.
      (* 追加ここから *)
      by apply: limg_sub_lker.
      (* 追加ここまで *)
    Qed.

    Lemma b1c' :
      (limg q <= lker p)%VS.
    Proof.
      (* 追加ここから *)
      apply: limg_sub_lker => //=.
      by rewrite addrC.
      (* 追加ここまで *)
    Qed.

    Lemma limg_addv (f g : 'End(E)) :
      (limg (f + g)%R <= limg f + limg g)%VS.
    Proof.
      apply/subvP => x /memv_imgP [u _ ->].
      (* 追加ここから *)
      rewrite add_lfunE.
      by apply: memv_add; apply/memv_img/memvf.
      (* 追加ここまで *)
    Qed.

    Theorem b1 :
      limg (p + q) = (limg p + limg q)%VS.
      (*
        p + q が射影写像なら、Im (p + q) = Im p ⊕ Im q が成り立つ。
      *)
    Proof.
      apply/eqP; rewrite eqEsubv limg_addv /=.
      (*
        limg (p + q) = (limg p + limg q)%VS
        ↓
        ↓apply/eqP; rewrite eqEsubv.
        ↓
        (limg (p + q)%R <= limg p + limg q <= limg (p + q)%R)%VS
        ↓
        ↓rewrite limg_addv.
        ↓
        true && (limg p + limg q <= limg (p + q)%R)%VS
        ↓
        rewrite /=.
        ↓
        (limg p + limg q <= limg (p + q)%R)%VS
      *)
      apply/subvP => x /memv_addP [u Hu] [v Hv ->].
      (*
        (limg p + limg q <= limg (p + q)%R)%VS
        ↓
        ↓apply/subvP.
        ↓
        {subset (limg p + limg q)%VS <= limg (p + q)}
        ↓
        ↓move=> x.
        ↓
        x \in (limg p + limg q)%VS -> x \in limg (p + q)
        ↓
        ↓move/memv_addP.
        ↓
        (exists2 u : E, u \in limg p & exists2 v : E, v \in limg q & x = u + v) ->
        x \in limg (p + q)
        ↓
        ↓case => u Hu.
        ↓
        (exists2 v : E, v \in limg q & x = u + v) -> x \in limg (p + q)
        ↓
        ↓case => v Hv ->.
        ↓
        u + v \in limg (p + q)
      *)
      have -> : u + v = (p + q) (u + v).
        rewrite lfun_simp !linearD /=.
        (*
          u + v = (p + q) (u + v)
          ↓
          ↓rewrite lfun_simp.
          ↓
          u + v = p (u + v) + q (u + v)
          ↓
          ↓rewrite !linearD.
          ↓
          u + v = lfun_linear p u + lfun_linear p v + (lfun_linear q u + lfun_linear q v)
          ↓
          ↓rewrite /=.
          ↓
          u + v = p u + p v + (q u + q v)
        *)
        rewrite (proj1 (proj_idE p)) // (proj1 (proj_idE q) _ v) //.
        (*
          u + v = p u + p v + (q u + q v)
          ↓
          ↓rewrite (proj1 (proj_idE p)) //.
          ↓
          ______________________________________(1/4)
          u + v = u + p v + (q u + q v)
          ______________________________________(2/4)
          projection p ← これと、
          ______________________________________(3/4)
          u \in limg p ← これは try done により証明完了する。
          ↓
          ↓rewrite (proj1 (proj_idE q) _ v) //.
          ↓
          ______________________________________(1/4)
          u + v = u + p v + (q u + v)
          ______________________________________(2/4)
          projection q ← これと、
          ______________________________________(3/4)
          v \in limg q ← これは try done により証明完了する。
        *)
      (* 追加ここから *)
        move: (Hv); rewrite memvE.
        move/subv_trans.
        move/(_ (lker p)) => H.
        move: (H b1c').
        rewrite -memvE memv_ker => /eqP ->. (* v \in lker p を導いて、p v を 0 に書き換えた。*)
        move: (Hu); rewrite memvE.
        move/subv_trans.
        move/(_ (lker q)) => H'.
        move: (H' b1c).
        rewrite -memvE memv_ker => /eqP ->. (* u in lker q を導いて、q u を 0 に書き換えた。 *)
        by rewrite addr0 add0r.
      by apply/memv_img/memvf.
      (*
        (p + q) (u + v) \in limg (p + q)
        ↓
        ↓apply/memv_img.
        ↓
        u + v \in fullv
        ↓
        ↓apply/memvf
        ↓
        No more subgoals
      *)
      (* 追加ここまで *)
    Qed.

    Theorem b2 :
      lker (p + q) = (lker p :&: lker q)%VS.
      (*
        p + q が射影写像なら、Ker (p + q) = Ker p ∩ Ker q が成り立つ。
      *)
    Proof.
      apply/vspaceP => x.
      (*
        lker (p + q) = (lker p :&: lker q)%VS.
        ↓
        ↓apply/vspaceP.
        ↓
        lker (p + q) =i (lker p :&: lker q)%VS
        ↓
        ↓move=> x.
        ↓
        (x \in lker (p + q)) = (x \in (lker p :&: lker q)%VS)
      *)
      rewrite memv_cap !memv_ker.
      (*
        (x \in lker (p + q)) = (x \in (lker p :&: lker q)%VS)
        ↓
        ↓rewrite memv_cap.
        ↓
        (x \in lker (p + q)) = (x \in lker p) && (x \in lker q)
        ↓
        ↓rewrite !memv_ker.
        ↓
        ((p + q) x == 0) = (p x == 0) && (q x == 0)
      *)
      rewrite add_lfunE.
      (*
        ((p + q) x == 0) = (p x == 0) && (q x == 0)
        ↓
        ↓rewrite add_lfunE.
        ↓
        (p x + q x == 0) = (p x == 0) && (q x == 0)
      *)
      case Hpx: (p x == 0).
      (* 追加ここから *)
      - move: (Hpx) => /eqP -> /=.
        by rewrite add0r.
      - rewrite /=.
        admit.
      (* 追加ここまで *)
    Admitted.

  End b.

End Problem2.
