Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Essentials.HoTT_Facts.
Require Import Category.Main.
Require Import Basic_Cons.CCC.
Require Import Coq_Cats.Type_Cat.Type_Cat.

(* Local Obligation Tactic := basic_simpl; auto. *)

(* if we use (unit : set) as terminal object then the level of arrows in Type_Cat
is brought down to set which cuases problems in working with Type_Cat, e.g.,
for showing Type_Cat has a subobject classifier. 
*)

(*
Program Instance unit_Type_term : Terminal Type_Cat :=
{
  terminal := unit;
  t_morph := fun _ _=> tt
}.

Next Obligation. (* t_morph_unique *)
Proof.
  extensionality x.
  destruct (f x); destruct (g x); reflexivity.
Qed.
 *)
(*
Parameter UNIT : Type.

Parameter TT : UNIT.

Axiom UNIT_SINGLETON : ∀ x y : UNIT, x = y.
*)
(** The type unit in coq is the terminal object of category of types. *)
Program Definition unit_Type_term : Terminal Type_Cat.
Proof.
  refine
    (
      @Build_Terminal
        Type_Cat
        HSUnit
        (fun _ _ => tt)
        _
    ).
  intros d f g.
  extensionality x.
  match goal with [|- ?A = ?B] => destruct A; destruct B; trivial end.
Defined.

Existing Instance unit_Type_term.

Definition ProductType (A B : Type_Cat) : hSet.
Proof.
  refine
    (
      @BuildTruncType 0 (A * B)%type _
    ).
  apply Prod_Trunc.
  apply A.
  apply B.
Defined.  

(** The cartesian product of types is the categorical notion of products in category of types. *)
Program Definition prod_Product (A B : Type_Cat) : @Product Type_Cat A B.
Proof.
  refine
    (
      @Build_Product
        Type_Cat
        A
        B
        (ProductType A B)
        fst
        snd
        (fun p x y z => (x z, y z))
        _
        _
        _
    ); auto
  .
  intros p' r1 r2 f g H1 H2 H3 H4.
    extensionality x.
    repeat
      match goal with
        [H : _ = _ |- _] =>
        apply (fun p => equal_f p x) in H
      end.
    basic_simpl.  
    destruct (f x); destruct (g x); cbn in *; ElimEq; trivial.
Defined.

Program Instance Type_Cat_Has_Products : Has_Products Type_Cat := prod_Product.

Definition ExpType (A B : Type_Cat) : hSet.
Proof.
  refine
    (
      @BuildTruncType 0 (A → B)%type _
    ).
Defined.                                        

(** The function type in coq is the categorical exponential in the category of types. *)
Program Definition fun_exp (A B : Type_Cat) : @Exponential Type_Cat _ A B.
Proof.
    refine
    (
      @Build_Exponential
        Type_Cat
        _
        A
        B
        (ExpType A B)
        (fun x => (fst x) (snd x))
        (fun h z u v=>  z (u, v))
        _
        _
    ); auto
  .
  intros z f u u' H1 H2.
  extensionality a; extensionality x.
  repeat
    match goal with
      [H : _ = _ |- _] =>
      apply (fun p => equal_f p (a, x)) in H
    end.
  transitivity (f (a, x)); cbn in *; auto.
Defined.

(* fun_exp defined *)

Program Instance Type_Cat_Has_Exponentials : Has_Exponentials Type_Cat := fun_exp.

(* Category of Types is cartesian closed *)

Instance Type_Cat_CCC : CCC Type_Cat.
Proof.
  refine
    (
      Build_CCC _ _ _ _
    ).
Defined.