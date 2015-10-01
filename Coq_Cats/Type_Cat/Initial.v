Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Essentials.HoTT_Facts.
Require Import Category.Main.
Require Import Basic_Cons.Terminal.
Require Import Coq_Cats.Type_Cat.Type_Cat.

Local Obligation Tactic := program_simpl; auto 3.

(** The empty type is the initial object of category of types. *)
Program Definition Empty_init : Initial Type_Cat.
Proof.
  refine
    (
      @Build_Terminal
        ((Type_Cat)^op)
        (@BuildTruncType _ _ Empty_HSet)
        _
        _
    ); cbn; auto.
Defined.