Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Functor Functor.Functor_Ops.

Local Open Scope functor_scope.

(** Cat, the category of (small) categories, is a category whose objects are (small) categories
and morphisms are functors.

In this development, the (relative) smallness/largeness is represented by universe levels and
universe polymorphism of Coq.
 *)

(** In general, functors betwen two categories (morphisms of Cat) don't always form an Hset.
Thus, we construct the category of categories whose object types form an HSet. In this case,
we can prove that the functors between them do form an HSet.
*)
Definition Cat : Category :=
{|
  Obj := {C : Category & IsHSet C};

  Hom := fun C D => Functor (C.1) (D.1);

  compose := fun C D E => Functor_compose;
  
  assoc := fun C D E F (G : (C.1) –≻ (D.1)) (H : (D.1) –≻ (E.1)) (I : (E.1) –≻ (F.1)) =>
            @Functor_assoc _ _ _ _ G H I;

  assoc_sym := fun C D E F (G : (C.1) –≻ (D.1)) (H : (D.1) –≻ (E.1)) (I : (E.1) –≻ (F.1)) =>
            inverse (@Functor_assoc _ _ _ _ G H I);

  id := fun C => Functor_id (C.1);

  id_unit_left := fun C D => @Functor_id_unit_left (C.1) (D.1);

  id_unit_right := fun C D => @Functor_id_unit_right (C.1) (D.1);

  Hom_HSet := fun C D => @CoDom_Cat_HSet_Functor_HSet (C.1) (D.1) (D.2)
|}.