(* Equivalence of CS4 and HK4*)
Require Import Coq.Program.Equality.
Require Import ModalLogic.
Require Export CS4.
Require Export HK4.
Require Import Context.


(* From Gilbert to Gentzen *)

Lemma nd_thyp_last: forall (D G:ctx) (A:Formula),
                       ND_Proof D (G,A) A.
Proof.
auto.
Qed.

Hint Resolve nd_thyp_last.


Lemma Ax0_CS: forall (D G:ctx) (A:Formula), ND_Proof D G (A ==> A).
Proof.
intros.
apply nd_intro.
auto.
Qed.

Hint Resolve Ax0_CS.


Lemma Ax1_CS: forall (D G:ctx) (A B:Formula), 
           ND_Proof D G (A ==> (B ==> A)).
Proof.
intros.
repeat apply nd_intro.
auto.
Qed.

Hint Resolve Ax1_CS.


Lemma Ax2_CS: forall (D G:ctx) (A B:Formula), 
           ND_Proof D G ( (A ==> (A ==> B)) ==> (A ==> B)).
Proof.
intros.
repeat apply nd_intro.
eapply nd_apply.
Focus 2.
apply nd_thyp_last.
eapply nd_apply.
Focus 2.
apply nd_thyp_last.
auto.
Qed.

Hint Resolve Ax2_CS.


Lemma Ax3_CS: forall (D G:ctx) (A B C:Formula), 
           ND_Proof D G ( (A ==> (B ==> C)) ==> (B ==> (A ==> C))).
Proof.
intros.
repeat apply nd_intro.
eapply nd_apply.
Focus 2.
apply (nd_elem_thyps _ _ B).
auto.
eapply nd_apply.
Focus 2.
apply nd_thyp_last.
auto.
Qed.

Hint Resolve Ax3_CS.

Lemma Ax4_CS: forall (D G:ctx) (A B C:Formula), 
           ND_Proof D G ( (B ==> C) ==> 
                            ( (A ==> B) ==> (A ==> C)) ).
Proof.
intros.
repeat apply nd_intro.
eapply nd_apply.
apply nd_elem_thyps.
auto.
eapply nd_apply.
apply nd_elem_thyps.
auto.
auto.
Qed.

Hint Resolve Ax4_CS.


(* Theorem 5.1 From axiomatic to natural deduction proofs.*)
Theorem HK_to_CS:
  forall (G: ctx) (A: Formula),
  (G |- A) -> (ND_Proof empty G A).
Proof.
intros.
dependent induction H ; auto.
eapply nd_apply.
eapply ctx_weak_R.
exact IHDeriv2.
apply ctx_weak_L.
assumption.
Qed.

Hint Resolve HK_to_CS.



(* From Getzen to Gilbert *)

Lemma boxtrans: 
forall (G:ctx) (A B:Formula),
G |- (#(#A) ==> B) -> G |- (#A ==> B).
Proof.
intros.
assert(K:=Ax4 empty A).
rewrite <- (ctx_empty_conc G).
eapply trans_dett.
exact K.
exact H.
Qed.

Hint Resolve boxtrans.

Lemma GenNec_swap: forall (D:ctx) (A:Formula),
      boxed D |-A -> 
         forall (G:ctx), G; boxed D |- Box A.
Proof.
intro.
induction D; auto.
intros.
  simpl in H.
  apply T2_deductionTh in H.
  eapply IHD in H.
  apply b1_dett in H.
  apply boxtrans in H.
  simpl.
  eauto.
Qed.

Hint Resolve GenNec_swap.


(* Lemma 5.2 General Neccesitation *)
Lemma GenNec: forall (D:ctx) (A:Formula),
      boxed D |-A -> 
         forall (G:ctx), boxed D; G |- Box A.
Proof.
intros.
apply ctx_permutation.
auto.
Qed.

Hint Resolve GenNec.


(* Theorem 5.3 From natural deduction to axiomatic proofs *)
Theorem CS_to_HK:
  forall (D: ctx) (G: ctx) (A: Formula),
  (ND_Proof D G A) -> boxed D;G |- A.
Proof.
intros.
dependent induction H.
- apply Hip.
  intuition.
- rewrite boxed_conc.
  rewrite <- (ctx_empty_conc ((boxed (D, B); boxed D'); G)).
  eapply (MP _ empty).
  Focus 2.
  apply (AxT _ B).
  simpl.
  intuition.
- simpl in IHND_Proof.
  apply T2_deductionTh.
  assumption.
- apply ctx_contraction.
  eapply MP.
  * exact IHND_Proof2.
  * assumption.
- apply GenNec.
  simpl in IHND_Proof.
  assumption.
- simpl in IHND_Proof2.
  apply T2_deductionTh_genPremise in IHND_Proof2.
  apply ctx_contraction.
  eapply MP.
  * exact IHND_Proof1.
  * assumption.
Qed.

Hint Resolve CS_to_HK.