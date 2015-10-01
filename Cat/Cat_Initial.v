Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Basic_Cons.Terminal.
Require Import Archetypal.Discr.Discr.

Local Hint Extern 1 => cbn in *.
Local Hint Extern 1 => match goal with [c : Empty |- _] => destruct c end.

(** The unique functor from the initial category to any other. *)
Program Definition Functor_From_Empty_Cat (C' : Category) : (0 –≻ C')%functor :=
{|
  FO := fun x => Empty_rect _ x;
  FA := fun a b f => match a as _ return _ with end
|}.

Definition EmptyCat_Cat : Cat.
Proof.
  refine (existT _ 0%category _).
  intros [].
Defined.

(** Empty Cat is the initial category. *)
Definition Cat_Init : Initial Cat.
Proof.
  refine
    (
      Build_Terminal
        (Cat ^op)
        EmptyCat_Cat
        (fun x => Functor_From_Empty_Cat x.1)
        _
    ); auto
  .
Defined.
