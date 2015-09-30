Require Import Category.Main.
Require Import Coq_Cats.Coq_Cat.
Require Import Essentials.HoTT_Facts.

(** The category of Types (Coq's "Type")*)

Program Definition Type_Cat : Category := Coq_Cat hSet.