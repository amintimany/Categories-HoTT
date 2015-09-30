Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Essentials.HoTT_Facts.
Require Import Category.Main.


(**
Fro categories C and C', a functor F : C -> C' consists of an arrow map from objects of C to objects of C' and an arrow map from arrows of C to arrows of C' such that an arrow h : a -> b is mapped to (F h) : F a -> F b.

Furthermore, we require functors to map identitiies to identities. Additionally, the immage of the coposition of two arrows must be the same as composition of their images.
*)
Record Functor (C C' : Category) : Type := 
{
  (** Object map *)
  FO : C → C';

  (** Arrow map *)
  FA : ∀ {a b}, (a –≻ b)%morphism → ((FO a) –≻ (FO b))%morphism;

  (** Mapping of identities *)
  F_id : ∀ c, FA (id c) = id (FO c);
  
  (** Functor commuting with composition *)
  F_compose : ∀ {a b c} (f : (a –≻ b)%morphism) (g : (b –≻ c)%morphism),
      (FA (g ∘ f) = (FA g) ∘ (FA f))%morphism

  (* F_id and F_compose together state the fact that functors are morphisms of categories (preserving the structure of categories!)*)
}.

Arguments FO {_ _} _ _.
Arguments FA {_ _} _ {_ _} _, {_ _} _ _ _ _.
Arguments F_id {_ _} _ _.
Arguments F_compose {_ _} _ {_ _ _} _ _.

Notation "C –≻ D" := (Functor C D) : functor_scope.

Bind Scope functor_scope with Functor.

Notation "F '_o'" := (FO F) : object_scope.

Notation "F '@_a'" := (@FA _ _ F) : morphism_scope.

Notation "F '_a'" := (FA F) : morphism_scope.

Hint Extern 2 => (apply F_id).

Local Open Scope morphism_scope.
Local Open Scope object_scope.

Ltac Functor_Simplify :=
  progress
    (
      repeat rewrite F_id;
      (
        repeat
          match goal with
          | [|- ?F _a ?A = id (?F _o ?x)] =>
            (rewrite <- F_id; (cbn+idtac))
          | [|- (id (?F _o ?x)) = ?F _a ?A] =>
            (rewrite <- F_id; (cbn+idtac))
          | [|- ?F _a ?A ∘ ?F _a ?B = ?F _a ?C ∘ ?F _a ?D] =>
            (repeat rewrite <- F_compose; (cbn+idtac))
          | [|- ?F _a ?A ∘ ?F _a ?B = ?F _a ?C] =>
            (rewrite <- F_compose; (cbn+idtac))
          | [|- ?F _a ?C = ?F _a ?A ∘ ?F _a ?B] =>
            (rewrite <- F_compose; (cbn+idtac))
          | [|- context [?F _a ?A ∘ ?F _a ?B]] =>
            (rewrite <- F_compose; (cbn+idtac))
          end
      )
    )
.

Hint Extern 2 => Functor_Simplify.

Section Functor_eq_simplification.

  Context {C C' : Category} (F G : (C –≻ C')%functor).
  
  (** Two functors are equal if their object maps and arrow maps are. *)
  Lemma Functor_eq_simplify (Oeq : F _o = G _o) :
    ((fun x y => match Oeq in _ = V return ((x –≻ y) → ((V x) –≻ (V y)))%morphism with idpath => F  @_a x y end) = G @_a) -> F = G.
  Proof.
    destruct F as [Fo Fa Fi Fc]; destruct G as [Go Ga Gi Gc].
    basic_simpl.
    ElimEq.
    doHomPIR.
    trivial.
  Defined.

  (** Extensionality for arrow maps of functors. *)
  Theorem FA_extensionality (Oeq : F _o = G _o) :
    (
      ∀ (a b : Obj)
        (h : (a –≻ b)%morphism),
        (
          fun x y =>
            match Oeq in _ = V return
                  ((x –≻ y) → ((V x) –≻ (V y)))%morphism
            with
              idpath => F  @_a x y
            end
        ) _ _ h = G _a h
    )
    →
    (
      fun x y =>
        match Oeq in _ = V return
              ((x –≻ y) → ((V x) –≻ (V y)))%morphism
        with
          idpath => F  @_a x y
        end
    ) = G @_a.
  Proof.
    auto.
  Defined.
  
  (** Fucntor extensionality: two functors are equal of their object maps are equal and their arrow maps are extensionally equal. *)
  Lemma Functor_extensionality (Oeq : F _o = G _o) :
    (
      ∀ (a b : Obj) (h : (a –≻ b)%morphism),
        (
          fun x y =>
            match Oeq in _ = V return
                  ((x –≻ y) → ((V x) –≻ (V y)))%morphism
            with
              idpath => F  @_a x y
            end
        ) _ _ h = G _a h
    ) → F = G.
  Proof.
    intros H.
    apply (Functor_eq_simplify Oeq); trivial.
    apply FA_extensionality; trivial.
  Defined.

End Functor_eq_simplification.

Hint Extern 2 => Functor_Simplify.

Ltac Func_eq_simpl :=
  match goal with
    [|- ?A = ?B :> Functor _ _] =>
    (apply (Functor_eq_simplify A B (idpath : A _o = B _o)%object)) +
    (cut (A _o = B _o)%object; [
       let u := fresh "H" in
       intros H;
         apply (Functor_eq_simplify A B H)
         |
    ])
  end.

Hint Extern 3 => Func_eq_simpl.

(** Given two categories C and D if the objects of D form a HSet then the type of functors
C –≻ D also form a HSet.

We prove this by estabilishing a left inverse for the Functor_extensionality and showing that
the codomain type of Functor extensionenatilty forms a HSet.
*)
Section CoDom_Cat_HSet_Functor_HSet.
  Context
    (C D : Category)
    {DHS : IsHSet D}
  .

  Lemma Functor_extensionality_inv
        {F G : Functor C D}
        (HO : F _o = G _o)
        (H : F = G)
    :
      (
        ∀ (a b : Obj) (h : (a –≻ b)%morphism),
          (
            fun x y =>
              match HO in _ = V return
                    ((x –≻ y) → ((V x) –≻ (V y)))%morphism
              with
                idpath => F  @_a x y
              end
          ) _ _ h = G _a h
      ).
  Proof.
    destruct H.
    match type of HO with
      ?A = ?B =>
      match type of A with
        ?U =>
        let H := fresh "H" in
        assert (H : IsHSet U);
          [
            repeat (apply @trunc_forall; [typeclasses eauto|intros ?x]);
            refine DHS
          |
          rewrite (@center _ (H _ _ HO idpath)); clear H
          ]
      end
    end.
    trivial.
  Defined.    
  
  Theorem Functor_extensionality_inv_is_left_inverse
          (F G : Functor C D)
          (HO : F _o = G _o)
          (H : F = G)
    :
      Functor_extensionality _ _ HO (Functor_extensionality_inv HO H) = H
  .
  Proof.
    destruct H.
    match type of HO with
      ?A = ?B =>
      match type of A with
        ?U =>
        let H := fresh "H" in
        assert (H : IsHSet U);
          [
            repeat (apply @trunc_forall; [typeclasses eauto|intros ?x]);
            refine DHS
          |
          rewrite (@center _ (H _ _ HO idpath)); clear H
          ]
      end
    end.
    unfold Functor_extensionality; unfold FA_extensionality.
    match goal with
      [|- _ _ _ _ ?A = _] =>
      generalize A as H'
    end.
    intros H'.
    match type of H' with
      ?A = ?B =>
      match type of A with
        ?U =>
        let H := fresh "H" in
        assert (H : IsHSet U);
          [
            repeat (apply @trunc_forall; [typeclasses eauto|intros ?x]);
            refine (Hom_HSet)
          |
          rewrite (@center _ (H _ _ H' idpath)); clear H H'
          ]
      end
    end.
    cbn.
    repeat rewrite (@contr _ _ idpath).
    trivial.
  Qed.
    
  Theorem CoDom_Cat_HSet_Functor_HSet : IsHSet (Functor C D).
  Proof.
    intros f g H1 H2.
    destruct H1.
    cbn in *.
    assert
      (
        Hc :
          IsHProp
            (
               ∀ (a b : Obj) (h : (a –≻ b)%morphism),
                 (
                   fun x y =>
                     match f_equal FO H2 in _ = V return
                           ((x –≻ y) → ((V x) –≻ (V y)))%morphism
                     with
                       idpath => f  @_a x y
                     end
                 ) _ _ h = f _a h
            )
      ).
    {
      repeat (apply @trunc_forall; [typeclasses eauto|intros ?x]);
      refine (Hom_HSet _ _).
    }
    {
      apply
        (
          @left_inv_equi_trunc
            (f = f)
            _
            _
            Hc
            (Functor_extensionality_inv (f_equal FO H2))
            (Functor_extensionality _ _ (f_equal FO H2))
            (Functor_extensionality_inv_is_left_inverse _ _ (f_equal FO H2))
            idpath
            H2
        ).
    }
  Qed.

End CoDom_Cat_HSet_Functor_HSet.