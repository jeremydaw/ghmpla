(** Hilbert style System HK4 from
  ''Does the deduction theorem fail for modal logic?'' 
   Sara Negri & Raul Hakli (2012)
   *)

Require Import Coq.Program.Equality.
Require Import ModalLogic.
Require Import Omega.
Require Import Context.

(** --------------- INFERENCE RULES --------------- *)
(** System HK for modal logic with local hypotheses, 
  without negation but extended with modal axioms for T and 4.
  As remarked by the authors, there is no substitution rule,
  the axiom schemata is used to perform implicit substitutions 
  giving instances of axioms whenever it is needed 
*)


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


(** 
 Verification of statements in the article and 
 in addition other useful lemmas, 
 some of them are the dettached versions of the axioms
 *)

Lemma AxI: 
  forall (G:ctx) (A:Formula), G |- (A ==> A).
Proof.
intros.
assert (H := AxK empty A A).
assert (H1:= AxW G A A).
rewrite <- (ctx_conc_empty G).
eapply MP in H1.
- exact H1.
- exact H.
Qed.

Hint Resolve AxI.


Lemma AxC_dett: 
  forall (G:ctx) (A B C:Formula),
  G |- (A ==> B ==> C) -> G |- (B ==> A ==> C).
Proof.
intros.
rewrite <- (ctx_empty_conc G).
eapply MP.
- exact H.
- intuition.
Qed.

Hint Resolve AxC_dett.


(* Theorem 4.2 Deduction *)
Theorem DeductionTh: 
  forall (G: ctx) (A B: Formula), (G,A) |- B -> G |- (A ==> B).
Proof.
intros G A B H.
dependent induction H; rewrite <- (ctx_empty_conc G).
- apply elem_inv in H.
  destruct H.
  + rewrite H.
    apply AxI.
  + eapply (MP _ _ A0 (A==> A0)); intuition.
- eapply (MP _ _ (A0 ==> B ==> A0) _); apply AxK.
- eapply (MP _ _ ((A0 ==> A0 ==> B) ==> A0 ==> B)).
  apply AxW.
  apply AxK.
- eapply (MP _ _ ((A0 ==> B ==> C) ==> B ==> A0 ==> C) _).
  apply AxC.
  apply AxK.
- eapply (MP _ _ ((B ==> C) ==>(A0 ==> B) ==> A0 ==> C) _ ).
  apply AxB.
  apply AxK.
- eapply (MP _ _ (# (A0 ==> B) ==> # A0 ==> # B) _).
  apply AxBoxK.
  apply AxK.
- eapply (MP _ _ (# A0 ==> A0) _).
  apply AxT.
  apply AxK.
- eapply (MP _ _ (# A0 ==> # # A0) _).
  apply Ax4.
  apply AxK.
- rewrite ctx_empty_conc.
  assert(X:=x).
  apply ctx_decomposition in x.
  destruct x.
  + destruct H1.
    rewrite H2 in H0.
    apply IHDeriv2 in H2.
    apply AxC_dett in H2.
    rewrite H1 in H.
    rewrite <- (ctx_conc_empty G).
    eapply MP.
    -- exact H.
    -- assumption.
  + destruct H1.
    assert (W := H1).
    apply IHDeriv1 in H1.
    rewrite W in X.
    simpl in X.
    inversion X.
    assert (empty |- ((A0 ==> B) ==> (A ==>A0) ==> (A ==> B))); intuition.
    assert (G' |- ((A ==> A0) ==> A ==> B)).
    -- eapply MP in H2.
       Focus 2.
       exact H0.
       rewrite (ctx_empty_conc G') in H2.
       exact H2.
    -- eapply MP.
    exact H1.
    exact H4.
    (* this subproof leaves an unsolved and unfocused goal !!!
    eapply (MP _ _ (A ==>A0) (A ==> B)).
    -- exact H1.
    -- rewrite <- (ctx_empty_conc G').
       eapply (MP G' empty (A0 ==> B) ((A ==> A0) ==> A ==> B) _).
       apply AxB. *)
- eapply MP. 
  + apply Nec.
    exact H.
  + apply AxK.
Qed. 

Hint Resolve DeductionTh.


(* Corollary 4.3  Multiple Discharge*)
Corollary multihyp_discharge:
  forall (n:nat) (G: ctx) (A B: Formula),
  G;(replicate A n) |- B -> G |- (A==>B).
Proof.
intros.
dependent induction n; simpl in H ; rewrite <- (ctx_empty_conc G). 
- eapply (MP _ _ B (A ==> B)).
  + assumption.
  + apply AxK.
- apply DeductionTh in H.
  apply IHn in H.
  eauto.
Qed.

Hint Resolve multihyp_discharge.


(* Corollary 4.4 Substitution or closure under composition *)
Corollary substitution:
  forall (G G': ctx) (A B: Formula),
  (G |- A) -> (G',A |- B) -> (G';G |- B).
Proof.
intros.
apply DeductionTh in H0.
eapply MP.
- exact H.
- exact H0.
Qed.

Hint Resolve substitution.


(* Theorem 4.5 Inverse Deduction*)
Theorem inverseDT:
  forall (G: ctx) (A B: Formula), G |- (A ==> B) -> G,A |- B.
Proof.
intros.
assert ((empty,A)|- A); intuition.
change (G,A) with (G; (empty,A)).
eapply MP.
exact H0.
exact H.
Qed.

Hint Resolve inverseDT.


(* Theorem 4.6 General Deduction Theorem*)
Theorem deductionTh_genPremise: 
  forall (G' G: ctx) (A B: Formula), (G,A);G' |- B -> G;G' |- (A ==> B).
Proof.
intro.
induction G' ; auto.
intros.
simpl in H.
apply DeductionTh in H.
apply IHG' in H.
apply AxC_dett in H.
apply inverseDT in H.
auto.
Qed.

Hint Resolve deductionTh_genPremise.


(* Lemma 4.7 Context Permutation *)
Lemma ctx_permutation: 
  forall (G G':ctx) (A:Formula), G;G' |- A -> G';G |- A.
Proof.
intro G.
induction G.
- intros.
  simpl.
  rewrite ctx_empty_conc in H.
  assumption.
- intros.
  simpl.
  apply inverseDT.
  apply IHG.
  apply deductionTh_genPremise in H.
  assumption.
Qed.

Hint Resolve ctx_permutation.


Corollary contraction_hyp:
  forall (G : ctx) (A B : Formula), (G, A), A |- B -> G, A |- B.
Proof.
intros.
apply inverseDT.
repeat apply DeductionTh in H.
assert(K:= AxW empty A B).
rewrite <- (ctx_empty_conc G).
eapply MP.
exact H.
assumption.
Qed.

Hint Resolve contraction_hyp.


Lemma AxW_dett: forall (G:ctx) (A B:Formula),
                G |- (A ==> A ==> B) -> G |- (A ==> B).
Proof.
intros.
auto.
Qed.

Hint Resolve AxW_dett.


(* Lemma 4.8 Context Contraction *)
Lemma ctx_contraction: 
  forall (G:ctx) (A:Formula), G;G |- A -> G |- A.
Proof.
intro.
induction G.
- auto.
- intros.
  apply deductionTh_genPremise in H.
  simpl in H.
  apply DeductionTh in H.
  apply AxW_dett in H.
  apply inverseDT.
  apply IHG.
  assumption.
Qed.

Hint Resolve ctx_contraction.


Lemma transitivity:
  forall (G: ctx) (A B C: Formula),
  G |- ((A ==> B) ==> ((B ==> C) ==> (A==> C))).
Proof.
intros.
rewrite <- (ctx_empty_conc G).
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


Lemma Axb1_dett: 
  forall (G:ctx) (A B:Formula), (G |- #(A ==> B)) -> G|- (#A ==> #B).
Proof.
intros.
rewrite <- (ctx_empty_conc G).
eapply MP.
- exact H.
- apply AxBoxK.
Qed.

Hint Resolve Axb1_dett.
