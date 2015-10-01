Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Essentials.HoTT_Facts.
Require Import Category.Main.
Require Import Basic_Cons.Product.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := basic_simpl; auto 2.

Definition SumType (A B : Type_Cat) : hSet.
Proof.
  refine
    (
      @BuildTruncType 0 (A + B)%type _
    ).
Defined.
  
(** The sum of types in coq is the categorical notion of sum in category of types. *)
Program Definition sum_Sum (A B : Type_Cat) : @Sum Type_Cat A B.
Proof.
  refine
    (
      @Build_Product
        (Type_Cat^op)
        A
        B
        (SumType A B)
        inl
        inr
        (
          fun p'
              r1
              r2
              x =>
            match x return p' with
            | inl a => r1 a
            | inr b => r2 b
            end
        )
        _
        _
        _
    ); auto.
  intros p' r1 r2 f g H1 H2 H3 H4.
  rewrite <- H3 in H1.
  rewrite <- H4 in H2.
  clear H3 H4.
  extensionality x.
  destruct x;
    match goal with
        [|- f (?m ?y) = g (?m ?y)] =>
        apply (@equal_f _ _ (fun x => f (m x)) (fun x => g (m x)))
    end; auto.
Defined.

(* sum_Sum defined *)

Program Instance Type_Cat_Has_Sums : Has_Sums Type_Cat := sum_Sum.

