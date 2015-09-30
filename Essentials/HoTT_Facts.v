Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.

Require Export HoTT.Basics.Trunc.
Require Export HoTT.Types.Forall.

Section left_inv_equi_contr.
  Context
    {A B : Type}
    (Bc : Contr B)
    {f : A → B}
    {g : B → A}
    (Hd : ∀ x, g (f x) = x)
  .

  Theorem f_equal_inv
          {a b : A}
          (u : a = b)
    :
      match Hd a in _ = x return x = _ with
        idpath =>
        match Hd b in _ = y return _ = y with
          idpath =>
          f_equal g (f_equal f u)
        end
      end
      = u
  .
  Proof.
    destruct u.
    cbn.
    destruct (Hd a).
    trivial.
  Defined.

  Theorem left_inv_equi_contr : Contr A.
  Proof.
    refine (BuildContr _ (g (@center _ Bc)) _).
    intros y.
    match goal with
      [|- ?A = ?B] =>
      rewrite <- (Hd A);
        rewrite <- (Hd B)
    end.
    apply f_equal.
    match goal with
      [|- ?A = ?B] =>
      transitivity (@center _ Bc);
        [symmetry|]; apply (@contr _ Bc)
    end.
  Qed.

End left_inv_equi_contr.

Section left_inv_equi_trunc.
  Context
    {A B : Type}
    (n : trunc_index)
    (Bc : IsTrunc n B)
    {f : A → B}
    {g : B → A}
    (Hd : ∀ x, g (f x) = x)
  .

  Theorem left_inv_equi_trunc : IsTrunc n A.
  Proof.
    revert A B f g Bc Hd.
    induction n as [|t]; clear n.
    {
      intros.
      eapply left_inv_equi_contr; eauto.
    }
    {
      intros A B f g Bt Hd.
      intros x y.
      assert (H := @f_equal_inv _ _ _ _ Hd x y).
      set (W := @f_equal _ _ f x y).
      set (V :=
             fun u =>
               match Hd x in _ = m return m = _ with
                 idpath =>
                 match Hd y in _ = n return _ = n with
                   idpath =>
                   @f_equal _ _ g (f x) (f y) u
                 end
               end
          ).
      apply (IHt _ _ W V).
      apply Bt.
      intros u.
      unfold V, W; clear V W.
      apply (f_equal_inv Hd u).
    }
  Qed.

End left_inv_equi_trunc.


Section eq_sig_morph.
  Context
    {A : Type}
    {P : A → hProp}
  .

  Definition eq_sig_morph_eq_morph
             {h h' : sigT P}
             (H : h = h')
    : projT1 h = projT1 h'
  .
  Proof.
    destruct H.
    reflexivity.
  Defined.

  Definition eq_morph_eq_sig_morph
             {h h' : sigT P}
             (H : projT1 h = projT1 h')
    : h = h'
  .
  Proof.
    destruct h as [x Hx].
    destruct h' as [y Hy].
    cbn in H.
    destruct H.
    destruct (@center _ (istrunc_trunctype_type (P x) Hx Hy)).
    reflexivity.
  Defined.

Theorem eq_sig_morph_eq_morph_inv
          {h h' : sigT P}
          (H : h = h')
    : eq_morph_eq_sig_morph (eq_sig_morph_eq_morph H) = H
  .
  Proof.
    unfold eq_sig_morph_eq_morph, eq_morph_eq_sig_morph.
    destruct H.
    destruct h as [x Hx].
    rewrite (@contr _ (istrunc_trunctype_type (P x) Hx Hx) idpath).
    reflexivity.
  Defined.

  Theorem eq_morph_eq_sig_morph_inv
          {h h' : sigT P}
          (H : projT1 h = projT1 h')
    : eq_sig_morph_eq_morph (eq_morph_eq_sig_morph H) = H
  .
  Proof.
    unfold eq_sig_morph_eq_morph, eq_morph_eq_sig_morph.
    destruct h as [x Hx]; destruct h' as [y Hy].
    cbn in *.
    destruct H.
    destruct (@center _ _).
    reflexivity.
  Defined.

  Theorem sig_f_equal_inv
          {h h' : sigT P}
          (H H': h = h')
          (u : H = H')
    :
      match eq_sig_morph_eq_morph_inv H in _ = x return x = _ with
        idpath =>
        match eq_sig_morph_eq_morph_inv H' in _ = y return _ = y with
          idpath =>
          f_equal eq_morph_eq_sig_morph (f_equal eq_sig_morph_eq_morph u)
        end
      end
      = u
  .
  Proof.
    destruct u.
    destruct H.
    cbn.
    destruct h as [x Hx].
    destruct Overture.internal_paths_rew_r.
    trivial.
  Defined.
  
End eq_sig_morph.
  
Section HSet_then_sig_HProp_HSet.
  Context
    {A : hProp}
    {P : A → hProp}
  .
  
  Theorem HProp_then_sig_HProp_HProp : IsHProp (sig P).
  Proof.
    intros [x Hx] [y Hy].
    cbn in *.
    refine (BuildContr _ _ _).
    destruct (@center _ (istrunc_trunctype_type A x y)).
    destruct (@center _ (istrunc_trunctype_type (P x) Hx Hy)).
    trivial.
    intros u.
    cbn.
    destruct (@center _ (istrunc_trunctype_type A x y)).
    destruct (@center _ (istrunc_trunctype_type (P x) Hx Hy)).
    rewrite <- (eq_sig_morph_eq_morph_inv 1).
    rewrite <- (eq_sig_morph_eq_morph_inv u).
    apply f_equal.
    transitivity ((@center _ (istrunc_trunctype_type A x x)));
      [symmetry|];
      apply ((@contr _ (istrunc_trunctype_type A x x)) _).
  Qed.

End HSet_then_sig_HProp_HSet.


Section Trunc_then_sig_HProp_Trunc.
  Context
    {n : trunc_index}
    {A : (n.+1)-Type}
    (P : A → hProp)
  .
  
  Theorem Trunc_then_sig_HProp_Trunc : IsTrunc n.+1 (sig P).
  Proof.
    induction n as [|t]; clear n.
    apply HProp_then_sig_HProp_HProp.
    intros x y h h'.
    specialize
      (IHt
         (@BuildTruncType _ _ (istrunc_trunctype_type A (x.1) (y.1)))
         (fun u => HUnit)
         (exist (fun u => Unit) (eq_sig_morph_eq_morph h) tt)
         (exist (fun u => Unit) (eq_sig_morph_eq_morph h') tt)
      ).
    destruct x as [x Hx]; destruct y as [y Hy].
    assert (W := f_equal projT1 h).
    cbn in W.
    destruct W.
    destruct (@center _ (istrunc_trunctype_type (P x) Hx Hy)).
    transparent
      assert
      (g :
         (
           (
             (exist (fun u => Unit) (eq_sig_morph_eq_morph h) tt)
             = (exist (fun u => Unit) (eq_sig_morph_eq_morph h') tt)
           ) → h = h'
         )
      ).
    {
      intros H.
      rewrite <- (eq_sig_morph_eq_morph_inv h).
      rewrite <- (eq_sig_morph_eq_morph_inv h').
      apply f_equal.
      exact (f_equal pr1 H).
    }
    eapply
      (
        @left_inv_equi_trunc
          _
          _
          _
          IHt
          (
            fun w =>
              ((f_equal (fun v => (f_equal projT1 v; tt)) w))
          )
          g
      ).
    intros u.
    destruct u.
    unfold g; clear g.
    unfold Overture.internal_paths_rew.
    cbn in *.
    destruct (eq_sig_morph_eq_morph_inv h).
    trivial.
  Qed.

End Trunc_then_sig_HProp_Trunc.

Section Prod_Contr.
  Context
    {A B : Type}
    (CA : Contr A)
    (CB : Contr B)
  .

  Definition eq_componens_eq (x y : A * B) (H : x = y) : ((fst x = fst y) * (snd x = snd y)).
  Proof.
    refine (f_equal fst H, f_equal snd H).
  Defined.

  Definition componens_eq_eq (x y : A * B) (H : (fst x = fst y) * (snd x = snd y)) : x = y.
  Proof.
    refine (@pair_eq _ _ _ _ (fst H) (snd H)).
  Defined.

  Theorem eq_componens_eq_left_inv (x y : A * B) (H : x = y) :
    componens_eq_eq x y (eq_componens_eq x y H) = H.
  Proof.
    destruct H.
    destruct x.
    trivial.
  Qed.
  
  Theorem Prod_Contr : Contr (A * B).
  Proof.
    refine (BuildContr _ (@center _ CA, @center _ CB) _).
    intros [y1 y2].
    apply pair_eq; apply contr.
  Qed.

End Prod_Contr.


Section Prod_Trunc.
  Context
    {n : trunc_index}
    {A B : Type}
    (HA : IsTrunc n A)
    (HB : IsTrunc n B)
  .
    
  Theorem Prod_Trunc : IsTrunc n (A * B).
  Proof.
    revert A B HA HB.
    induction n as [|t]; clear n.
    intros; apply Prod_Contr; trivial.
    intros A B HA HB [x1 x2] [y1 y2].
    assert (Ht : IsTrunc t ((x1 = y1) * (x2 = y2))).
    {
      apply IHt.
      apply HA.
      apply HB.
    }
    {
      apply (
          @left_inv_equi_trunc
            ((x1, x2) = (y1, y2))
            ((x1 = y1) * (x2 = y2))
            t
            Ht
            (eq_componens_eq (x1, x2) (y1, y2))
            (componens_eq_eq (x1, x2) (y1, y2))
            (eq_componens_eq_left_inv (x1, x2) (y1, y2))
        ).
    }
  Qed.

End Prod_Trunc.