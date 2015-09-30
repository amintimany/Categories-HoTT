Require Import Essentials.Notations.
Require Import Essentials.Types.
Require Import Essentials.Facts_Tactics.
Require Import Category.Main.
Require Import Ext_Cons.Prod_Cat.Prod_Cat.
Require Import Functor.Main.
Require Import Basic_Cons.Product.
Require Import Basic_Cons.Exponential.

Local Obligation Tactic := idtac.
(**
The exponential functor maps each pair of objects (a, b) (an object of product category Cᵒᵖ × C -> C) to the exponential bᵃ.
*)
Program Definition Exp_Func {C : Category}
        {hp : Has_Products C}
        (exps : ∀ a b, Exponential a b)
: ((C^op × C) –≻ C)%functor :=
{|
  FO := fun x => exps (fst x) (snd x);
  FA := fun a b f => 
           Exp_morph_ex _ _ ((snd f) ∘ (eval _) ∘ ((Prod_Func C) @_a (_, fst b) (_, fst a) (id (exps (fst a) (snd a)), fst f)))%morphism
|}.

Next Obligation. (* F_id *)
Proof.
  basic_simpl.
  eapply Exp_morph_unique.
  rewrite <- Exp_morph_com.
  reflexivity.
  simpl; simpl_ids; reflexivity.
Qed.

Next Obligation. (* F_compose *)
Proof.
  intros.
  eapply Exp_morph_unique.
  rewrite <- Exp_morph_com; reflexivity.
  rewrite Prod_compose_id.
  rewrite F_compose.
  rewrite <- (assoc _ _ (eval _)).
  rewrite <- Exp_morph_com.
  repeat rewrite assoc.
  rewrite <- F_compose.
  rewrite <- Prod_cross_compose.
  rewrite F_compose.
  match goal with
      [|- _ = (?X ∘ ?A ∘ ?B ∘ _)%morphism] =>
      rewrite (assoc_sym _ _ X);
        rewrite (assoc_sym _ _ (X ∘ A));
        rewrite (assoc _ _ X)
  end. 
  rewrite <- Exp_morph_com.
  repeat rewrite assoc.
  rewrite <- F_compose.
  cbn; auto.
Qed.

(* Exponential_Functor defined *)
