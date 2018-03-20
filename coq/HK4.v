(* Hilbert style System HK from
   Sara Negri & Raul Hakli
 *)

Require Import Coq.Program.Equality.
Require Import ModalLogic.
Require Import Omega.
Require Import Context.

(* HK extended with axioms for T and 4, 
   modal logic with local hypotheses *)
(* it remains the axioms for possibility and negation *)
(* | Ax5: forall (G: ctx) (A: Formula), 
       Deriv G ((Not(Not A)) ==> A)  *)
(* as remarked by the authors, there is no substitution rule,
  the axiom schemata is used to perform implicit substitutions 
  giving instances of axioms whenever it is needed *)


Inductive Deriv: ctx -> Formula -> Prop:=
| Hip:  forall (G : ctx) (A: Formula), 
          elem A G -> Deriv G A 
      
| AxK:  forall (G: ctx) (A B: Formula), 
        Deriv G (A ==> (B ==> A))
       
| AxW:  forall (G: ctx) (A B: Formula), 
        Deriv G ((A ==> (A ==> B)) ==> (A ==> B))
       
| AxC:  forall (G: ctx) (A B C: Formula), 
        Deriv G ((A ==> (B ==> C)) ==> (B ==>(A ==> C)))
       
| AxB:  forall (G: ctx) (A B C: Formula), 
        Deriv G ((B ==> C) ==> ((A ==> B) ==> (A ==> C)))
       
| AxBoxK: forall (G: ctx) (A B: Formula), 
        Deriv G (Box(A ==> B) ==> ((Box A) ==> (Box B)))
        
| AxT: forall (G : ctx) (A : Formula),
        Deriv G ((Box A) ==> A)
       
| Ax4: forall (G : ctx) (A : Formula),
        Deriv G ((Box A) ==> (Box(Box A)))
       
| MP:   forall (G G': ctx) (A B: Formula),
        Deriv G A -> Deriv G' (A ==> B) -> Deriv (G';G) B
      
| Nec:  forall (G: ctx) (A: Formula), 
        Deriv empty A -> Deriv G (Box A).
       
Hint Constructors Deriv.


Notation "G |- A" := (Deriv G A) (at level 30).


Lemma Ax0: forall (G:ctx) (A:Formula),
              G |- (A ==> A).
Proof.
intros.
assert(H:=AxK empty A A).
assert(H1:=AxW G A A).
change G with (G;empty).
eauto.
Qed.

Hint Resolve Ax0.


Lemma AxC_dett: forall (G:ctx) (A B C:Formula),
                G |- (A ==> B ==> C) -> G |- (B ==> A ==> C).
Proof.
intros.
replace G with (empty;G).
eapply MP.
exact H.
intuition.
apply ctx_empty_conc.
Qed.

Hint Resolve AxC_dett.


(* Theorem 4.2 Deduction *)
Theorem T2_deductionTh: 
  forall (G: ctx) (A B: Formula), (G,A) |- B -> G |- (A ==> B).
Proof.
intros G A B H.
dependent induction H.
- apply elem_inv in H.
  destruct H.
  + rewrite H.
    apply Ax0.
  + rewrite <- (ctx_empty_conc G).
    eapply MP.
    Focus 2.
    apply AxK.
    intuition.
- rewrite <- (ctx_empty_conc G).
  eapply MP.
  Focus 2.
  apply AxK.
  apply AxK.
- rewrite <- (ctx_empty_conc G).
  eapply MP.
  Focus 2.
  apply AxK.
  apply AxW.
- rewrite <- (ctx_empty_conc G).
  eapply MP.
  Focus 2.
  apply AxK.
  apply AxC.
- rewrite <- (ctx_empty_conc G).
  eapply MP.
  Focus 2.
  apply AxK.
  apply AxB.
- rewrite <- (ctx_empty_conc G).
  eapply MP.
  Focus 2.
  apply AxK.
  apply AxBoxK.
- rewrite <- (ctx_empty_conc G).
  eapply MP.
  Focus 2.
  apply AxK.
  apply AxT.
- rewrite <- (ctx_empty_conc G).
  eapply MP.
  Focus 2.
  apply AxK.
  apply Ax4.
- assert(K:=x).
  apply ctx_decomposition in x.
  destruct x.
  + destruct H1.
    rewrite H2 in H0.
    apply IHDeriv2 in H2.
    apply AxC_dett in H2.
    rewrite <- (ctx_conc_empty G).
    eapply MP.
    rewrite H1 in H.
    exact H.
    assumption.
  + destruct H1.
    assert (W := H1).
    apply IHDeriv1 in H1.
    rewrite W in K.
    simpl in K.
    inversion K.
    assert (empty |- ((A0 ==> B) ==> (A ==>A0) ==> (A ==> B))).
    intuition.
    assert (G' |- ((A ==> A0) ==> A ==> B)).
    eapply MP in H2.
    Focus 2.
    exact H0.
    rewrite (ctx_empty_conc G') in H2.
    exact H2.
    eapply MP.
    exact H1.
    exact H4.
- rewrite <- (ctx_empty_conc G). 
  eapply MP.
  * apply Nec.
    exact H.
  * apply AxK.
Qed. 

Hint Resolve T2_deductionTh.


(* Corollary 4.3  Multiple Discharge*)
Lemma AxC3_multihyp:
  forall (n:nat) (G: ctx) (A B: Formula),
  G;(replicate A n) |- B -> G |- (A==>B).
Proof.
intros.
dependent induction n.
- simpl in H.
  rewrite <- (ctx_empty_conc G). 
  eapply MP.
  Focus 2.
  apply AxK.
  assumption.
- simpl in H.
  apply T2_deductionTh in H.
  apply IHn in H.
  rewrite <- (ctx_empty_conc G).
  eauto.
Qed.

Hint Resolve AxC3_multihyp.


(* Corollary 4.4 Substitution *)
Lemma AxC4_cut:
  forall (G G': ctx) (A B: Formula),
  (G |- A) -> (G',A |- B) -> (G';G |- B).
Proof.
intros.
apply T2_deductionTh in H0.
eapply MP.
exact H.
exact H0.
Qed.

Hint Resolve AxC4_cut.


(* Theorem 4.5 Inverse Deduction*)
Lemma T5_reverseDT:
  forall (G: ctx) (A B: Formula),
  G |- (A ==> B) -> G,A |- B.
Proof.
intros.
assert ((empty,A)|- A); intuition.
change (G,A) with (G; (empty,A)).
eapply MP.
exact H0.
exact H.
Qed.

Hint Resolve T5_reverseDT.


(* Theorem 4.6 General Deduction Theorem*)
Theorem T2_deductionTh_genPremise: 
  forall (G' G: ctx) (A B: Formula), (G,A);G' |- B -> G;G' |- (A ==> B).
Proof.
intro.
induction G' ; auto.
intros.
simpl in H.
apply T2_deductionTh in H.
apply IHG' in H.
apply AxC_dett in H.
apply T5_reverseDT in H.
auto.
Qed.

Hint Resolve T2_deductionTh_genPremise.


(* Lemma 4.7 Context Permutation *)
Lemma ctx_permutation: forall (G G':ctx) (A:Formula),
         G;G' |- A -> G';G |- A.
Proof.
intro G.
induction G.
- intros.
  simpl.
  rewrite ctx_empty_conc in H.
  assumption.
- intros.
  simpl.
  apply T5_reverseDT.
  apply IHG.
  apply T2_deductionTh_genPremise in H.
  assumption.
Qed.

Hint Resolve ctx_permutation.


Lemma AxC6_contraction_hyp:
  forall (G : ctx) (A B : Formula), (G, A), A |- B -> G, A |- B.
Proof.
intros.
apply T5_reverseDT.
repeat apply T2_deductionTh in H.
assert(K:= AxW empty A B).
rewrite <- (ctx_empty_conc G).
eapply MP.
exact H.
assumption.
Qed.

Hint Resolve AxC6_contraction_hyp.


Lemma AxW_dett: forall (G:ctx) (A B:Formula),
                G |- (A ==> A ==> B) -> G |- (A ==> B).
Proof.
intros.
auto.
Qed.

Hint Resolve AxW_dett.

Hint Resolve AxW_dett.

(* Lemma 4.8 Context Contraction *)
Lemma ctx_contraction: forall (G:ctx) (A:Formula),
                 G;G |- A -> G |- A.
Proof.
intro.
induction G.
- auto.
- intros. 
  apply T2_deductionTh_genPremise in H.
  simpl in H.
  apply T2_deductionTh in H.
  apply AxW_dett in H.
  apply T5_reverseDT.
  apply IHG.
  assumption.
Qed.

Hint Resolve ctx_contraction.


Lemma transitivity:
  forall (G: ctx) (A B C: Formula),
  G |- ((A ==> B) ==> ((B ==> C) ==> (A==> C))).
Proof.
intros.
replace G with (empty;G).
Focus 2. intuition.
eapply MP.
Focus 2.
eapply AxC.
intuition.
Qed.

Hint Resolve transitivity. 


Lemma trans_dett:
  forall (G G': ctx)(P Q R : Formula),
  G |- (P ==> Q) -> G' |- (Q ==> R) -> (G;G') |- (P ==> R).
Proof.
intros.
assert (K:= transitivity empty P Q R).
rewrite <- (ctx_empty_conc G).
eapply MP.
- exact H0.
- eapply MP.
  exact H.
  assumption.
Qed.

Hint Resolve trans_dett.


Lemma b1_dett: forall (G:ctx) (A B:Formula),
                (G |- #(A ==> B)) -> G|- (#A ==> #B).
Proof.
intros.
rewrite <- (ctx_empty_conc G).
eapply MP.
exact H.
apply AxBoxK.
Qed.

Hint Resolve b1_dett.
