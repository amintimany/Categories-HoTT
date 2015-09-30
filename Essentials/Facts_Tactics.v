Require Import Essentials.Notations.
Require Import Essentials.Types.

Require Export Coq.Program.Tactics.

Require Export HoTT.Basics.Overture.

Ltac basic_simpl :=
  let simpl_prod _ :=
      match goal with
        [H : prod _ _ |- _] =>
        let H1 := fresh H "1" in
        let H2 := fresh H "2" in
        destruct H as [H1 H2]
      end
  in
  let simpl_sig _ :=
      match goal with
        [H : @sig _ _ |- _] =>
        let H1 := fresh H "1" in
        let H2 := fresh H "2" in
        destruct H as [H1 H2]
      end
  in
  let basic_simpl_helper _ :=
      cbn in *; intros;
        repeat simpl_prod tt;
        repeat simpl_sig tt
  in
  repeat basic_simpl_helper tt
.

Global Obligation Tactic := basic_simpl; auto.

Definition f_equal {A B : Type} (f : A → B) {x y : A} (H : x = y) : f x = f y
  :=
    match H in _ = u return
          _ = f u
    with
      idpath => idpath
    end
.

Definition equal_f {A B : Type} {f g : A → B} (H : f = g) : ∀ x : A, f x = g x
  :=
    fun x =>
      match H in _ = u return
            _ = u x
      with
        idpath => idpath
      end
.

(** A tactic to apply proof irrelevance on all proofs of the same type in the context. *)
(*
Ltac PIR :=
  let pir_helper _ :=
      match goal with
      |[H : ?A, H' : ?A|- _] =>
       match type of A with
       | Prop =>
         destruct (proof_irrelevance _ H H')
       end
      end
  in
  repeat pir_helper tt
.
*)
(** A tactic to eliminate equalities in the context. *)
Ltac ElimEq := repeat match goal with [H : _ = _|- _] => destruct H end.

Hint Extern 1 => progress ElimEq.

(** A tactic to simplify terms before rewriting them. *)

Ltac cbn_rewrite W := 
  let H := fresh "H" in
  set (H := W); cbn in H; rewrite H; clear H
.

Ltac cbn_rewrite_in W V := 
  let H := fresh "H" in
  set (H := W); cbn in H; rewrite H in V; clear H
.
                                                
Ltac cbn_rewrite_back W := 
  let H := fresh "H" in
  set (H := W); cbn in H; rewrite <- H; clear H
.

Ltac cbn_rewrite_back_in W V := 
  let H := fresh "H" in
  set (H := W); cbn in H; rewrite <- H in V; clear H
.

Tactic Notation "cbn_rewrite" constr(W) := cbn_rewrite W.
Tactic Notation "cbn_rewrite" constr(W) "in" hyp_list(V) := cbn_rewrite_in W V.
Tactic Notation "cbn_rewrite" "<-" constr(W) := cbn_rewrite_back W.
Tactic Notation "cbn_rewrite" "<-" constr(W) "in" hyp_list(V) := cbn_rewrite_back_in W V.

(** Equality on sigma type under proof irrelevance *)

Lemma sig_proof_irrelevance
      {A : Type}
      (P : A → Type)
      {PHProp : ∀ x, IsHProp (P x)}
      (X Y : sigT P)
  : proj1_sig X = proj1_sig Y → X = Y.
Proof.
  intros H.
  destruct X as [x Hx].
  destruct Y as [y Hy].
  cbn in *.
  destruct H.
  destruct (@center _ (PHProp x Hx Hy)).
  trivial.
Qed.

Hint Extern 2 (existT ?A _ _ = existT ?A _ _) => apply sig_proof_irrelevance.

(* Automating use of functional_extensionality *)

Monomorphic Axiom funxt : dummy_funext_type.
Global Instance funext : Funext := {dummy_funext_value := funxt}.

Tactic Notation "extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
    (apply (@path_forall funext _ _ X Y)) ; intro x
  end.

Ltac FunExt := 
progress (
    repeat (
        match goal with
          [|- _ = _] =>
          let x := fresh "x" in
          extensionality x
        end
      )
  )
.

Hint Extern 1 => FunExt.


Lemma pair_eq (A B : Type) (a b : A * B) : fst a = fst b → snd a = snd b → a = b.
Proof.
  intros H1 H2.
  refine
    (
      match H1 in _ = y return
            _ = (y, _)
      with
        idpath =>
        match H2 in _ = z return
              _ = (_, z)
        with
          idpath => idpath
        end
      end
    )
  .
Defined.  

Hint Resolve pair_eq. 

(** Tactics to apply a tactic to all hypothesis in an effiecient way. This is due to Jonathan's (jonikelee@gmail.com) message on coq-club *)

Ltac revert_clearbody_all :=
 repeat lazymatch goal with H:_ |- _ => try clearbody H; revert H end.

Ltac hyp_stack :=
 constr:($(revert_clearbody_all;constructor)$ : True).

Ltac next_hyp hs step last :=
 lazymatch hs with (?hs' ?H) => step H hs' | _ => last end.

Tactic Notation "dohyps" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := tac H; next_hyp hs step idtac in
 next_hyp hs step idtac.

Tactic Notation "dohyps" "reverse" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := next_hyp hs step idtac; tac H in
 next_hyp hs step idtac.

Tactic Notation "do1hyp" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := tac H + next_hyp hs step fail in
 next_hyp hs step fail.

Tactic Notation "do1hyp" "reverse" tactic3(tac) :=
 let hs := hyp_stack in
 let rec step H hs := next_hyp hs step fail + tac H in
 next_hyp hs step fail.

(** End of tactics for applying a tactic to all hypothesis. *)
