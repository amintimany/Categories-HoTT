Global Set Primitive Projections.

Global Set Universe Polymorphism.

Require Import HoTT.Basics.Overture.
Require Import HoTT.Basics.Trunc.

Definition HUnit : hProp.
Proof.
  apply (@BuildTruncType -1 Unit).
  intros x y.
  refine (@BuildContr _ _ _).
  destruct x; destruct y; trivial.
  intros u.
  destruct x.
  destruct u.
  trivial.
Defined.

(** The Empty Type. *)
Inductive Empty : Type :=.

Instance Empty_HProp : IsHProp Empty.
Proof.
  intros [].
Qed.

Definition Empty_HSet : IsHSet Empty.
Proof.
  typeclasses eauto.
  Show Proof.
Qed.

  
Hint Extern 1 =>
let tac := (repeat intros ?); match goal with [H : Empty |- _] => destruct H end in
match goal with
  | [|- context[Empty]] => tac
  | [H : context[Empty] |- _] => tac
end
.

(** The product type, defined as a record to enjoy eta rule for records. *)
Record prod (A B : Type) := {fst : A; snd : B}.

Arguments fst {_ _ } _.
Arguments snd {_ _ } _.
Arguments Build_prod {_ _ } _ _.

Notation "( X , Y )" := (Build_prod X Y).
Notation "X * Y" := (prod X Y) : type_scope.