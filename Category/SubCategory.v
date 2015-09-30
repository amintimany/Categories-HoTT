Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Essentials.HoTT_Facts.
Require Import Category.Category.

(**
A sub category of C is a category whose objects are a subset (here we sues subset types, i.e., sig) of objects of C and whose arrows are a subset of arrows of C.

Here, we define a subcategory using two functions Obj_Cri : Obj C -> Prop which defines the objects of subcategory and Hom_Cri : ∀ (a b : Obj) -> Hom a b -> Prop which defines the arrows of subcategory.
In other words, Obj_Cri and Hom_Cri are respectively cirteria for objects and arrows being in the sub category.
We furthermore, require that the Hom_Cri provides that identity arrows of all objects in the subcategory are part of the arrows of the subcategory. Additionally, For ant two composable arrow that are in the subcategory, their composition must also be in the subcategory.
*)
Section SubCategory.
  Context (C : Category)
          (Obj_Cri : Obj → Type)
          (Hom_Cri : ∀ a b, (a –≻ b)%morphism → hProp)
  .
  

  Arguments Hom_Cri {_ _} _.
  
  Context (Hom_Cri_id : ∀ a, Obj_Cri a → Hom_Cri (id a))
          (Hom_Cri_compose : ∀ a b c (f : (a –≻ b)%morphism) (g : (b –≻ c)%morphism),
              Hom_Cri f → Hom_Cri g → Hom_Cri (g ∘ f)).

  Arguments Hom_Cri_id {_} _.
  Arguments Hom_Cri_compose {_ _ _ _ _} _ _.

  Local Obligation Tactic := idtac.

  Program Definition SubCategory : Category :=
  {|
    Obj := sigT Obj_Cri;

    Hom :=
      fun a b =>
        sigT (@Hom_Cri (projT1 a) (projT1 b));

    compose :=
      fun _ _ _ f g =>
        existT _ _
              (Hom_Cri_compose (proj2_sig f) (proj2_sig g));

    id :=
      fun a =>
        existT _ _ (Hom_Cri_id (projT2 a))
  |}.

  Local Hint Extern 1 => apply istrunc_trunctype_type.

  Next Obligation.
  Proof.
    intros.
    cbn in *.
    apply sig_proof_irrelevance; cbn; auto.
  Qed.

  Next Obligation.
  Proof.
    cbn; intros.
    symmetry.
    apply SubCategory_obligation_1.
  Qed.

  Local Hint Extern 3 => simpl.
  
  Local Obligation Tactic := basic_simpl; auto.

  Solve Obligations.

  Next Obligation.
  Proof.
    apply
      (
        @Trunc_then_sig_HProp_Trunc
          (-1)
          ((@BuildTruncType 0 (a1 –≻ b1)%morphism (@Hom_HSet _ _ _)))
      ).
  Qed.

End SubCategory.


(**
A wide subcategory of C is a subcategory of C that has all the objects of C but not necessarily all its arrows.
*)
Notation Wide_SubCategory C Hom_Cri := (SubCategory C (fun _ => True) Hom_Cri).

(**
A Full subcategory of C is a subcategory of C that for any pair of objects of the category that it has, it has all the arrows between them. In practice, we construct a full subcategory by only expecting an object criterion and setting the arrow criterrion to accept all arrows.
*)
Notation Full_SubCategory C Obj_Cri := (SubCategory C Obj_Cri (fun _ _ _ => True) (fun _ _ => I) (fun _ _ _ _ _ _ _ => I)).