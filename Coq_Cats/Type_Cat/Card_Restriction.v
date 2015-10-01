Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Coq_Cats.Type_Cat.Type_Cat.

(** A cardinality restriction for types is a property that holds for a type if and only if it holds for all types isomorphic to it. *)
Record Card_Restriction : Type :=
{
  Card_Rest : Type → Prop;
  
  Card_Rest_Respect : ∀ (A B : Type), (A <~> B) → Card_Rest A → Card_Rest B
}.

Coercion Card_Rest : Card_Restriction >-> Funclass.

(*
(** A type is finite if it is isomorphic to a subset of natural numbers less than n for soem natural number n. *)
Program Definition Finite : Card_Restriction :=
  {|
    Card_Rest :=
      fun A => inhabited {n : nat & (A ≃≃ {x : nat | x < n} ::> Type_Cat)%isomorphism}
  |}.

Next Obligation.
Proof.
  destruct H as [[n I]].
  eexists.
  refine (existT _ n (I ∘ (X⁻¹)%isomorphism)%isomorphism).
Qed.
*)