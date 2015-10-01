Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Essentials.HoTT_Facts.
Require Import Category.Main.
Require Import Functor.Functor.
Require Import Coq_Cats.Type_Cat.Type_Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat.

Definition HomType {C : Category} (x y : C) : hSet.
Proof.
  refine (@BuildTruncType _ (x –≻ y)%morphism _).
  apply Hom_HSet.
Defined.

(** The hom-functor is a functor that maps a pair of objects (a, b) (an object of the product category Cᵒᵖ×C) to the type of arrows from a to b. *)
Definition Hom_Func (C : Category) : (((C^op) × C) –≻ Type_Cat)%functor.
Proof.
  refine
    (
      @Build_Functor
        ((C^op) × C)
        Type_Cat
        (fun x => @HomType C (fst x) (snd x))
        (fun x y f g => compose C (fst f) ((@compose (C^op) _ _ _) (snd f) g))
        _
        _
    ); cbn in *; auto
  .
Defined.


