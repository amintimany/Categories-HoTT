Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Essentials.HoTT_Facts.
Require Import Category.Main.
Require Import Functor.Functor.
Require Import Cat.Cat.
Require Import Coq_Cats.Type_Cat.Type_Cat.

(* empty and singleton categories *)

(** The empty category – initial object of Cat. *)
Definition EmptyCat : Category :=
  {|
    Obj := (Empty : Type);
    Hom := fun _ _ => (Unit : Type);
    compose := fun _ _ _ _ _ => tt;
    assoc := fun _ _ _ _ _ _ _ => idpath;
    assoc_sym := fun _ _ _ _ _ _ _ => idpath;
    id := fun _ => tt;
    id_unit_left :=
      fun _ _ h =>
        match h as u return (tt = u) with
        | tt => idpath
        end;
    id_unit_right :=
      fun _ _ h =>
        match h as u return (tt = u) with
        | tt => idpath
        end;
    Hom_HSet := fun x _ => match x with end
  |}.

(** The singleton category – terminal object of Cat. *)
Program Definition SingletonCat : Category :=
  {|
    Obj := (Unit : Type);
    Hom := fun _ _ => (Unit : Type);
    compose := fun _ _ _ _ _ => tt;
    assoc := fun _ _ _ _ _ _ _ => idpath;
    assoc_sym := fun _ _ _ _ _ _ _ => idpath;
    id := fun _ => tt;
    id_unit_left :=
      fun _ _ h =>
        match h as u return (tt = u) with
        | tt => idpath
        end;
    id_unit_right :=
      fun _ _ h =>
        match h as u return (tt = u) with
        | tt => idpath
        end;
    Hom_HSet := fun _ _ h h' => @trunc_contr _ _ (istrunc_trunctype_type HUnit h h')
  |}.
  
  
Notation "0" := (EmptyCat) : category_scope.
Notation "1" := (SingletonCat) : category_scope.

(* discrete categories in general *)
Section Discr.
  Context (obj : hSet).

  (** Discrete category – one in which has no arrow but identitities. 
Note that this definition is not necessarily a discrete cat in Coq as UIP is not
generally provable. We simply assume so by implicitly assuming object type to have UIP.
In HoTT terms, we assume obj to be a HSet. *)
  Program Definition Discr_Cat : Category :=
    {|
      Obj := obj;
      Hom := fun a b => a = b;
      compose := @concat _;
      id := fun a => idpath
    |}.
    
End Discr.

(*
Definition Type_n (n : nat) : Type := {x : nat | Tle x n}.

Notation "'Discr_n' n" := (Discr_Cat (Type_n n)) (at level 200, n bigint) : category_scope.
*)

(*
(** Any discrete category is ismorphic to its dual. *)
Section Discr_Cat_Dual_Iso.
  Context (obj : Type).

  Local Hint Extern 1 => progress cbn.
  
  Program Definition Discr_Cat_Dual_Iso :
    (Discr_Cat obj ≃≃ (Discr_Cat obj)^op ::> Cat)%isomorphism%category
    :=
      {|
        iso_morphism := {|FO := fun x => x; FA := fun _ _ h => eq_sym h|};
        inverse_morphism := {|FO := fun x => x; FA := fun _ _ h => eq_sym h|}
      |}.

End Discr_Cat_Dual_Iso.
 *)
(*
(** Any two isomorphic types form isomorphic discrete categories. *)
Section Discr_Cat_Iso.
  Context {obj obj' : Type} (I : (obj <~> obj' ::> Type_Cat)%isomorphism).

  Program Definition Discr_Cat_Iso :
    ((Discr_Cat obj) ≃≃ (Discr_Cat obj') ::> Cat)%isomorphism
    :=
      {|
        iso_morphism :=
          {|
            FO := iso_morphism I;
            FA :=
              fun c d h =>
                match h in _ = y return
                      (iso_morphism I c) = (iso_morphism I y)
                with
                  eq_refl => eq_refl
                end
          |};
        inverse_morphism :=
          {|
            FO := inverse_morphism I;
            FA :=
              fun c d h =>
                match h in _ = y return
                      (inverse_morphism I c) = (inverse_morphism I y)
                with
                  eq_refl => eq_refl
                end
          |}
      |}.

  Next Obligation.
  Proof.
    Func_eq_simpl.
    {
      FunExt; cbn in *.
      match goal with
        [|- ?A = ?B] => destruct A
      end.
      apply JMeq_eq; auto.      
    }
    {
      FunExt; cbn.
      cbn_rewrite (equal_f (left_inverse I)); trivial.
    }
  Qed.

  Next Obligation.
  Proof.
    Func_eq_simpl.
    {
      FunExt; cbn in *.
      match goal with
        [|- ?A = ?B] => destruct A
      end.
      apply JMeq_eq; auto.      
    }
    {
      FunExt; cbn.
      cbn_rewrite (equal_f (right_inverse I)); trivial.
    }
  Qed.
  
End Discr_Cat_Iso.
*)
(* Functor from SingletonCat to another category. *)
Section Func_From_SingletonCat.
  Context {C : Category} (Cobj : C).

  (** The functor from SingletonCat to C induced bo Cobj. *)
  Program Definition Func_From_SingletonCat : (SingletonCat –≻ C)%functor :=
    {|
      FO := fun _ => Cobj;
      FA := fun _ _ _ => id
    |}.

End Func_From_SingletonCat.

(* Discrete Functor *)
Section Discr_Func.
  Context {C : Category} {A : hSet} (Omap : A → C).

  (** The discrete functor – a functor from a discrete category of type A
 to a category C based on a function from A to objects of C. *)
  Program Definition Discr_Func : ((Discr_Cat A) –≻ C)%functor :=
    {|
      FO := Omap;
      
      FA := fun (a b : A) (h : a = b) =>
              match h in _ = y return ((Omap a) –≻ (Omap y))%morphism with
              | idpath => id
              end
    |}.

  (** The discrete-opposite functor – a functor from the opposite of a
discrete category of type A to a category C based on a function from A to objects of C. *)
  Program Definition Discr_Func_op : ((Discr_Cat A)^op –≻ C)%functor :=
    {|
      FO := Omap;
      FA := fun (a b : A) (h : b = a) =>
              match h in _ = y return ((Omap y) –≻ (Omap b))%morphism with
              | idpath => id
              end
    |}.
    
End Discr_Func.
  
Arguments Discr_Func {_ _} _, _ {_} _.
Arguments Discr_Func_op {_ _} _, _ {_} _.