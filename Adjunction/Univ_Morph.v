Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import NatTrans.Main.
Require Import Adjunction.Adjunction Adjunction.Duality.
Require Import Ext_Cons.Comma.
Require Import Basic_Cons.Terminal Basic_Cons.Facts.Term_IsoCat.
Require Import Cat.Cat_Iso.
Require Import Archetypal.Discr.Discr Archetypal.Discr.NatFacts.

(** A functor G : D –≻ C has a left adjoint if and only if
the comma category (Comma (Func_From_SingletonCat x) G) has
an initial object for any (x : C).

Dually, a functor F : C –≻ D has a right adjoint if and only
if the comma category (Comma F (Func_From_SingletonCat x)) 
has a terminal object for any (x : D).
 *)

(**
If the comma category (Comma (Func_From_SingletonCat x) G) has
an initial object for any (x : C). Then G : D –≻ C has
a left adjoint.
*)

Section Universal_Morphism_Right_Adjonit.
  Context
    {C D : Category}
    (G : (D –≻ C)%functor)
    (HU_init : ∀ (x : C), Initial (Comma (Func_From_SingletonCat x) G) )
  .

  Local Definition Universal_Morphism_Lem :
    ∀ c a h,
      CMH_right (t_morph (HU_init c) a) = CMH_right h
  .
  Proof.          
    intros c a h.
    apply f_equal.
    apply (t_morph_unique (HU_init c)).
  Qed.

  Local Ltac smart_apply_Universal_Morphism_Lem :=
    match goal with
      [|- CMH_right ?A = ?B] =>
      match type of A with
        ?W =>
        let M :=
            (eval cbn in W)
        in
        match M with
          Comma_Hom _ _ ?X ?Y =>
          evar (U : Comma_Hom _ _ X Y);
            replace B with (CMH_right ?U);
            [
              eapply
                (
                  Universal_Morphism_Lem
                    _
                    Y
                    (
                      Build_Comma_Hom
                        _
                        _
                        X
                        Y
                        tt
                        B
                        _
                    )
                )
            |
            reflexivity
            ]
        end
      end
    end.
    
  Program Definition Universal_Morphism_Right_Adjonit_Func : (C –≻ D)%functor
    :=
      {|
        FO :=
          fun c =>
            CMO_trg (terminal (HU_init c));
        FA :=
          fun c c' h =>
            CMH_right
              (t_morph
                 (HU_init c)
                 (@Build_Comma_Obj
                    _
                    _
                    _
                    (Const_Func 1 c)
                    G
                    tt
                    (CMO_trg (terminal (HU_init c')))
                    ((CMO_hom (terminal (HU_init c'))) ∘ h)%morphism
                 )
              )
      |}
  .

  Next Obligation.
  Proof.
    smart_apply_Universal_Morphism_Lem.
    Unshelve.
    cbn; auto.
  Qed.

  Next Obligation.
  Proof.
    smart_apply_Universal_Morphism_Lem.
    Unshelve.
    {
      cbn.
      rewrite F_compose.
      rewrite assoc.
      simpl_ids;
      match goal with
        [|- ((G _a) ((CMH_right ?A)) ∘ ((G _a) (CMH_right ?B)) ∘ _)%morphism = _] =>
        cbn_rewrite (CMH_com B);
          do 2 rewrite assoc_sym;
          cbn_rewrite (CMH_com A); auto
      end.
    }
  Qed.


  Local Obligation Tactic := idtac.

  
  Program Definition Universal_Morphism_Right_Adjonit_unit :
    (Functor_id C –≻ G ∘ Universal_Morphism_Right_Adjonit_Func)%nattrans
    :=
      {|
        Trans := fun c => CMO_hom (terminal (HU_init c))
      |}
  .

  Next Obligation.
  Proof.
    intros c c' h.
    cbn.
    match goal with
      [|- _ = (G _a (CMH_right ?A) ∘ _)%morphism] =>
      cbn_rewrite (CMH_com A)
    end.
    auto.
  Qed.

  Next Obligation.
  Proof.
    symmetry.
    apply Universal_Morphism_Right_Adjonit_unit_obligation_1.
  Qed.

    
  Program Definition Universal_Morphism_Right_Adjonit :
    (Universal_Morphism_Right_Adjonit_Func ⊣ G)%functor
    :=
      {|
        adj_unit := Universal_Morphism_Right_Adjonit_unit;
        adj_morph_ex :=
          fun c d f =>
            CMH_right
              (t_morph
                 (HU_init c)
                 (@Build_Comma_Obj
                    _
                    _
                    _
                    (Const_Func 1 c)
                    G
                    tt
                    d
                    f
                 )
              )
      |}
  .

  Next Obligation.
  Proof.
    intros c d f.
    cbn in *.
    match goal with
      [|- _ = (G _a (CMH_right ?A) ∘ _)%morphism] =>
      cbn_rewrite (CMH_com A)
    end.
    auto.
  Qed.

  Next Obligation.
  Proof.
    intros c d f g h H1 H2.
    cbn in *.
    rewrite <- (id_unit_right _ _ f) in H1, H2.
    symmetry in H1, H2.
    set (W :=
           @Build_Comma_Obj
             _
             _
             _
             (Const_Func 1 c)
             G
             tt
             d
             f
        )
    .
    let tac u H
        :=
        (
          change u with
          (
            CMH_right
              (  
                Build_Comma_Hom
                  _
                  _
                  (terminal (HU_init c))
                  W
                  tt
                  u
                  H
              )
          )
        )
    in
    tac g H1;
      tac h H2
    .
    transitivity (CMH_right (t_morph (HU_init c) W));
      [symmetry|];
      apply (Universal_Morphism_Lem c W)
    .
  Qed.

End Universal_Morphism_Right_Adjonit.

(**
if a functor G : D –≻ C has a left adjoint then the comma
category (Comma (Func_From_SingletonCat x) G) has
an initial object for any (x : C).
*)
Section Right_Adjoint_Universal_Morphism.
  Context
    {C D : Category}
    {F : (C –≻ D)%functor}
    {G : (D –≻ C)%functor}
    (Adj : (F ⊣ G)%functor)
    (x : C)
  .

  Program Definition Right_Adjoint_Universal_Morphism_terminal : (Comma (Func_From_SingletonCat x) G)
    :=
      {|
        CMO_src := tt;
        CMO_trg := (F _o x)%object;
        CMO_hom := Trans (adj_unit Adj) x
      |}
  .

  Program Definition Right_Adjoint_Universal_Morphism_t_morph
          (u : (Comma (Func_From_SingletonCat x) G))
    :
      Comma_Hom _ _ Right_Adjoint_Universal_Morphism_terminal u
    :=
      {|
        CMH_left := tt;
        CMH_right :=
          @adj_morph_ex
            _
            _
            _
            _
            Adj
            x
            (CMO_trg u)
            (CMO_hom u)
      |}
  .

  Next Obligation.
  Proof.  
    simpl_ids.
    symmetry.
    apply (@adj_morph_com _ _ _ _ Adj).
  Qed.
  
  
  Program Definition Right_Adjoint_Universal_Morphism : Initial (Comma (Func_From_SingletonCat x) G)
    :=
      {|
        terminal := Right_Adjoint_Universal_Morphism_terminal;
        t_morph := Right_Adjoint_Universal_Morphism_t_morph
      |}
  .

  Next Obligation.
  Proof.
    assert (Hf := CMH_com f).
    assert (Hg := CMH_com g).
    cbn in *.
    simpl_ids in Hf; simpl_ids in Hg.
    symmetry in Hf, Hg.
    apply Comma_Hom_eq_simplify.
    match goal with
      [|- ?A = ?B] =>
      destruct A; destruct B; trivial
    end.
    eapply (@adj_morph_unique _ _ _ _ Adj); eauto.
  Qed.

End Right_Adjoint_Universal_Morphism.

(**
If the comma category (Comma F (Func_From_SingletonCat x)) has
an initial object for any (x : D). Then F : D –≻ C has
a right adjoint.
*)
Section Universal_Morphism_Left_Adjonit.
  Context
    {C D : Category}
    (F : (C –≻ D)%functor)
    (HU_term : ∀ (x : D), Terminal (Comma F (@Func_From_SingletonCat D x)))
  .

  Definition Universal_Morphism_Left_Adjonit_HU_init
             (x : (D^op)%category)
    :
      Initial (Comma ((@Func_From_SingletonCat (D ^op) x)) (F^op))
    :=
      Term_IsoCat
        (
          Opposite_Cat_Iso
            (
              Isomorphism_Compose
                (Comma_Opposite_Iso F (@Func_From_SingletonCat D x))
                (Comma_Left_Func_Iso (@Func_From_SingletonCat_Opposite D x) (F ^op))
            )
        )
        (HU_term x)
  .

  Definition Universal_Morphism_Left_Adjonit
    :
      (F ⊣ (
               Universal_Morphism_Right_Adjonit_Func
                 (F ^op)
                 Universal_Morphism_Left_Adjonit_HU_init
             )^op
      )%functor
    :=
      Adjunct_Duality
        (
          @Universal_Morphism_Right_Adjonit
            (D^op)
            (C^op)
            (F^op)
            Universal_Morphism_Left_Adjonit_HU_init
        )
  .

End Universal_Morphism_Left_Adjonit.

(**
if a functor F : C –≻ D has a right adjoint then the comma
category (Comma F (Func_From_SingletonCat x)) has
an terminal object for any (x : D).
*)
Section Left_Adjoint_Universal_Morphism.
  Context
    {C D : Category}
    {F : (C –≻ D)%functor}
    {G : (D –≻ C)%functor}
    (Adj : (F ⊣ G)%functor)
    (x : D)
  .

  Definition Left_Adjoint_Universal_Morphism : Terminal (Comma F (Const_Func 1 x))
    :=
      Term_IsoCat
        (
          Opposite_Cat_Iso
            (
              Isomorphism_Compose
                (
                  Comma_Left_Func_Iso
                    (Inverse_Isomorphism (@Func_From_SingletonCat_Opposite D x))
                    (F ^op)
                )
                (Inverse_Isomorphism (Comma_Opposite_Iso F (@Func_From_SingletonCat D x)))
            )
        )
        (Right_Adjoint_Universal_Morphism (Adjunct_Duality Adj) x)
  .

End Left_Adjoint_Universal_Morphism.