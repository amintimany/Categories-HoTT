Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import NatTrans.NatTrans NatTrans.Operations.

Program Instance Func_Cat (C C' : Category) : Category :=
{
  Obj := Functor C C';

  Hom := NatTrans;

  compose := @NatTrans_compose _ _;

  id := @NatTrans_id _ _;

  assoc := fun _ _ _ _ _ _ _ => @NatTrans_compose_assoc _ _ _ _ _ _ _ _ _;
             
  assoc_sym := fun _ _ _ _ _ _ _ => eq_sym (@NatTrans_compose_assoc _ _ _ _ _ _ _ _ _);

  id_unit_right := @NatTrans_id_unit_right _ _;
  
  id_unit_left := @NatTrans_id_unit_left _ _
}.

Section Opposite_Func_Cat.
  Context (C D : Category).

  Instance Op_Func_Cat_to_Func_Cat_Op : Functor (Func_Cat C D)^op (Func_Cat C^op D^op) :=
    {
      FO := Opposite_Functor;
      FA := fun _ _ => Opposite_NatTrans;
      F_id := fun _ => NatTrans_id_Op _;
      F_compose := fun _ _ _ _ _ => NatTrans_compose_Op _ _ 
    }.

  Instance Func_Cat_Op_to_Op_Func_Cat : Functor (Func_Cat C^op D^op) (Func_Cat C D)^op :=
    {
      FO := Opposite_Functor;
      FA := fun _ _ => Opposite_NatTrans;
      F_id := fun F => NatTrans_id_Op F;
      F_compose := fun _ _ _ N N' => NatTrans_compose_Op N N'
    }.

  Program Instance Func_Cat_Op_Iso : (Func_Cat C D)^op ≡≡ (Func_Cat C^op D^op) ::> Cat :=
    {
      iso_morphism := Op_Func_Cat_to_Func_Cat_Op;
      inverse_morphism := Func_Cat_Op_to_Op_Func_Cat
    }.

  Next Obligation.
  Proof.
    match goal with
      [|- ?A = ?B] =>
      cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
    end.
    extensionality x; extensionality y; extensionality f.
    match goal with
      [|- match _ in _ = V return _ with eq_refl => ?A end f = ?B] =>
      transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A f end)
    end.
    destruct W; trivial.
    apply JMeq_eq.
    destruct W; trivial.
  Qed.

  Next Obligation.
  Proof.
    match goal with
      [|- ?A = ?B] =>
      cut(A _o = B _o); [intros W; apply (Functor_eq_simplify _ _ W)|]; trivial
    end.
    extensionality x; extensionality y; extensionality f.
    match goal with
      [|- match _ in _ = V return _ with eq_refl => ?A end f = ?B] =>
      transitivity (match W in _ = V return Hom (V x) (V y) with eq_refl => A f end)
    end.
    destruct W; trivial.
    apply JMeq_eq.
    destruct W; trivial.
  Qed.
  
End Opposite_Func_Cat.