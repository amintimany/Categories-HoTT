Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Basic_Cons.Product.

(** Product in category of categories is imply the product of actegories *)

Definition Cat_Prod (C C' : Cat) : Cat := ((C.1 × C'.1)%category; Prod_Cat_HSet _ _ (C.2) (C'.2)).

Definition Cat_Products (C C' : Cat) : @Product Cat C C'.
Proof.
  refine
    (
      Build_Product
        Cat
        C
        C'
        (Cat_Prod C C')
        (Cat_Proj1 C.1 C'.1)
        (Cat_Proj2 C.1 C'.1)
        (fun P => fun F G =>  Functor_compose (Diag_Func P.1) (Prod_Functor F G))
        _
        _
        _
    ); cbn; auto.
  intros p' r1 r2 f g H1 H2 H3 H4.
  cbn in *.
  transitivity (Functor_compose (Diag_Func p'.1) (Prod_Functor r1 r2)).
  + symmetry.
    rewrite <- H1, <- H2.
    apply Prod_Functor_Cat_Proj.
  + rewrite <- H3, <- H4.
    apply Prod_Functor_Cat_Proj.
Defined.

(* Cat_Products defined *)

Program Instance Cat_Has_Products : Has_Products Cat := Cat_Products.




