Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Functor.Main.
Require Import Cat.Cat.
Require Import Ext_Cons.Prod_Cat.Prod_Cat Ext_Cons.Prod_Cat.Operations.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.
Require Import NatTrans.NatTrans NatTrans.Func_Cat.
Require Import Cat.Cat_Product.

(** The exponential in cat is jsut the functor category. *)

Local Open Scope functor_scope. 

(** Evaluation functor. *)
Program Definition Exp_Cat_Eval (C C' : Cat) : ((Func_Cat C.1 C'.1) × C.1) –≻ C'.1 :=
{|
  FO := fun x => ((fst x) _o (snd x))%object;
  FA := fun A B f => (((fst B) _a (snd f)) ∘ (@Trans _ _ _ _ (fst f) _))%morphism
|}.

Next Obligation. (* F_compose *)
Proof.
  repeat rewrite F_compose.
  repeat rewrite assoc.
  match goal with
      [|- (?A ∘ ?B = ?A ∘ ?C)%morphism] => cut (B = C); [intros H; rewrite H; clear H|]; trivial
  end.
  repeat rewrite assoc_sym.
  match goal with
      [|- (?A ∘ ?B = ?C ∘ ?B)%morphism] => cut (A = C); [intros H; rewrite H; clear H|]; trivial
  end.
  rewrite Trans_com; trivial.
Defined.

(* Exp_Cat_Eval defined *)

(** The arrow map of curry functor. *)
Definition Exp_Cat_morph_ex_A
        {C C' C'' : Cat} (F : (C''.1 × C.1) –≻  C'.1)
        (a b : C''.1) (h : (a –≻ b)%morphism)
  :
    ((Fix_Bi_Func_1 a F) –≻ (Fix_Bi_Func_1 b F))%nattrans.
Proof.
  refine
    (
      @Build_NatTrans
        _
        _
        (Fix_Bi_Func_1 a F)
        (Fix_Bi_Func_1 b F)
        (fun c => (F @_a (_, _) (_, _) (h, id c))%morphism)
        _
        _
    ); cbn; auto.
Defined.

(* Exp_Cat_morph_ex_A defined *)

Local Hint Extern 1 => apply NatTrans_eq_simplify; cbn.

(** The curry functor. *)
Program Definition Exp_Cat_morph_ex
        {C C' C'' : Cat}
        (F : (C''.1 × C.1) –≻ C'.1)
  :
    C''.1 –≻ (Func_Cat C.1 C'.1) :=
{|
  FO := fun a => Fix_Bi_Func_1 a F;
  FA := Exp_Cat_morph_ex_A F
|}.

(** Proof that currying after uncurrying gives back the same functor. *)
Lemma Exp_cat_morph_ex_eval_id
      {C C' C'' : Cat}
      (u : C''.1 –≻ (Func_Cat C.1 C'.1))
  :
    (u =
     Exp_Cat_morph_ex
       (Exp_Cat_Eval C C'
                     ∘ Prod_Functor (u ∘ Cat_Proj1 C''.1 C.1)
                     (Functor_id C.1 ∘ Cat_Proj2 C''.1 C.1) ∘ 
                     Diag_Func (C''.1 × C.1))
    )%morphism.
Proof.
  Func_eq_simpl.
  {
    extensionality a; extensionality b; extensionality h; cbn.
    apply NatTrans_eq_simplify.
    extensionality m.
    transitivity
      (
        (
          match f_equal (fun w => ((w a) _o m)%object) H in _ = V return (V –≻ _)%morphism with
            idpath =>
            match f_equal (fun w => (w b) _o m)%object H in _ = U return (_ –≻ U)%morphism with
              idpath => Trans (u _a h)%morphism m
            end
          end
        )
      ).
    {
      destruct H; trivial.
    }      
    {
      match goal with
        [|- match ?X with idpath => match ?Y with idpath => _ end end = _] =>
        generalize X as H1;
          generalize Y as H2
      end.
      intros H1 H2.
      cbn in *.
      rewrite ( @center _ ((C'.2) _ _ H1 idpath)).
      rewrite ( @center _ ((C'.2) _ _ H2 idpath)).
      auto.
    }
  }
  {
    FunExt; cbn.
    Func_eq_simpl; cbn; auto.
  }
Qed.

(** The exponential for category of categories (functor categories). *)
Definition Cat_Exponential (C C' : Cat) : @Exponential Cat _ C C'.
Proof.
  refine
    (
      @Build_Exponential
        Cat
        _
        C
        C'
        (Func_Cat C.1 C'.1; @CoDom_Cat_HSet_Functor_HSet (C.1) (C'.1) (C'.2))
        (Exp_Cat_Eval C C')
        (fun C'' F => @Exp_Cat_morph_ex C C' C'' F)
        _
        _
    ); cbn.
  {
    intros z f.
    Func_eq_simpl.
    FunExt; cbn.
    rewrite <- F_compose; cbn.
    auto.
  }
  {
    intros z f u u' H1 H2.
    rewrite H1 in H2; clear H1.
    assert (H3 := @f_equal _ _ Exp_Cat_morph_ex _ _ H2); clear H2.
    cbn in *.
    repeat rewrite <- Exp_cat_morph_ex_eval_id in H3; trivial.
  }
Qed.

(* Cat_Exponentials defined *)

Program Instance Cat_Has_Exponentials : Has_Exponentials Cat := Cat_Exponential.
