(* Natural Deduction System CS4 from 
   Pfenning & Davies ...
 *)

(* Original development by Selene Linares  *)

Require Import Coq.Program.Equality.
Require Import ModalLogic.
Require Import Context.

(************* INFERENCE RULES ***************)

Inductive ND_Proof : ctx -> ctx -> Formula -> Prop :=

| nd_thyp : forall (D: ctx) (G G': ctx) (A: Formula),
             ND_Proof D ((G,A) ; G') A

| nd_vhyp : forall (D D': ctx) (G: ctx) (B: Formula),
             ND_Proof (D,B ; D') G B

| nd_intro : forall (D: ctx) (G: ctx) (A B: Formula),
             ND_Proof D (G,A) B -> ND_Proof D G (A ==> B)

| nd_apply : forall (D: ctx) (G: ctx) (A B: Formula),
             ND_Proof D G (A ==> B) -> 
             ND_Proof D G A-> ND_Proof D G B

| nd_boxI : forall (D: ctx) (G: ctx) (A: Formula),
             ND_Proof D empty A -> ND_Proof D G (Box A)

| nd_boxE : forall (D: ctx) (G: ctx) (A C: Formula),
             ND_Proof D G (Box A) -> ND_Proof (D,A) G C ->
             ND_Proof D G C
.

Hint Constructors ND_Proof.



(** -----------------STRUCTURAL RULES-------------------- **)


Lemma nd_elem_thyps: 
  forall (D: ctx) (G : ctx) (A: Formula), elem A G -> ND_Proof D G A.
Proof.
intros.
assert( exists G1, exists G2, G=(G1,A);G2 ).
- apply elem_ctxsplit.
  assumption.
- destruct H0 as [G1'].
  destruct H0 as [G2'].
  rewrite H0.
  apply nd_thyp.
Qed.

Hint Resolve nd_elem_thyps.


(* Lemma 3.4 Structural rules: Weakening *)
Lemma nd_weakening_thyps : 
  forall (D: ctx) (G G': ctx) (A: Formula),
  ND_Proof D (G ; G') A -> forall (B : Formula), ND_Proof D (G, B ; G') A.
Proof.
intros.
dependent induction H ; auto.
- apply nd_elem_thyps.
  assert(elem A (G;G')).
  rewrite <- x.
  intuition.
  apply elem_conc_split in H.
  destruct H.
  apply elem_conc_L.
  intuition.
  intuition.
- apply nd_intro.
  assert(K:= IHND_Proof G (G',A) eq_refl B0).
  simpl in K.
  assumption.
- eapply nd_apply.
  apply IHND_Proof1.
  apply IHND_Proof2.
- eapply nd_boxE.
  apply IHND_Proof1.
  apply IHND_Proof2.
Qed.

Hint Resolve nd_weakening_thyps.


Lemma nd_weak_last : 
  forall (D: ctx) (G: ctx) (A : Formula),
  ND_Proof D G A -> forall (B : Formula), ND_Proof D (G, B) A.
Proof.
intros.
change (G,B) with  ((G,B);empty).
auto.
Qed.

Hint Resolve nd_weak_last.


(* Lemma 3.5 Inversion of nd_intro*)
Lemma nd_intro_inv: forall (D G:ctx) (A B:Formula),
        ND_Proof D G (A ==> B) -> ND_Proof D (G,A) B.
Proof.
intros.
eapply nd_apply with A.
Focus 2.
eapply nd_elem_thyps.
intuition.
apply nd_weak_last.
apply H.
Qed.

Hint Resolve nd_intro_inv.

(* Lemma 3.4 Structural rules: Exchange *)
Lemma nd_exchange: forall (D G:ctx) (A B C:Formula),
        ND_Proof D ((G,A),B) C -> ND_Proof D ((G,B),A) C.
Proof.
intros.
repeat (apply nd_intro in H).
apply (nd_apply _ _ B C).
apply nd_intro_inv.
apply nd_weak_last.
assumption.
intuition.
Qed.

Hint Resolve nd_exchange.

(** STRUCTURAL CONTEXT RULES **)

(* Lemma 3.6 Weakening Right *)
Lemma ctx_weak_R: 
  forall (D: ctx) (G : ctx) (A: Formula), 
  ND_Proof D G A -> forall (G': ctx), ND_Proof D (G;G') A.
Proof.
intros.
induction G'; auto.
simpl.
auto.
Qed.

Hint Resolve ctx_weak_R.

(* Lemma 3.6 Weakening Left*)
Lemma ctx_weak_L: 
  forall (G: ctx) (D : ctx) (A: Formula), 
  ND_Proof D G A -> forall (G': ctx), ND_Proof D (G';G) A.
Proof.
intro.
induction G.
* intros.
  simpl.
  rewrite <- (ctx_empty_conc G').
  apply ctx_weak_R.
  assumption.
* intros.
  simpl.
  apply nd_intro_inv.
  apply IHG.
  apply nd_intro.
  assumption.
Qed.

Hint Resolve ctx_weak_L.


(* Lemma 3.6 Exchange snoc  *)
Lemma ctx_exch_snoc: forall (G' D G:ctx) (A B:Formula),
 ND_Proof D (G;(G',A)) B -> ND_Proof D ((G,A);G') B.
Proof.
intro.
induction G'.
- auto.
- intros.
  simpl.
  apply nd_intro_inv.
  apply IHG'.
  simpl.
  apply nd_intro.
  apply nd_exchange.
  simpl in H.
  assumption.
Qed.

Hint Resolve ctx_exch_snoc.


(* Lemma 3.6 Exchange conc *)
Lemma ctx_exch_conc: forall (G' D G:ctx) (A B:Formula),
 ND_Proof D ((G,A);G') B -> ND_Proof D (G;(G',A)) B.
Proof.
intro.
induction G'.
- auto.
- intros.
  simpl in H.
  apply nd_intro in H.
  apply IHG' in H.
  apply nd_intro_inv in H.
  change (G; ((G', f), A)) with
         (((G; G'), f), A).  
  change ((G; (G', A)), f) with
         (((G; G'), A), f) in H.
  apply nd_exchange.
  assumption.
Qed.

Hint Resolve ctx_exch_snoc.


(* Lemma 3.7 Generalized nd_intro*)
Lemma nd_intro_gen: forall (G' D G:ctx) (A B:Formula),
   ND_Proof D (G,A;G') B -> ND_Proof D (G;G') (A ==> B).
Proof.
intro.
induction G'.
- intros. auto.
- intros. 
  simpl in H.
  apply nd_intro.  
  apply ctx_exch_conc.
  assumption.
Qed.

Hint Resolve nd_intro_gen.


(* Lemma 3.8 Substitution *)
Theorem substitution:
  forall (D G: ctx) (A : Formula), (ND_Proof D G A) -> 
  forall (G':ctx) (J: Formula),  
    (ND_Proof D ((G,A);G') J) -> ND_Proof D (G;G') J.
Proof.
intros.
apply nd_intro_gen in H0.
eapply nd_apply.
exact H0.
apply ctx_weak_R.
assumption.
Qed.

Hint Resolve substitution.


Lemma nd_elem_vhyps: 
  forall (D: ctx) (G : ctx) (A: Formula), 
         elem A D -> ND_Proof D G A.
Proof.
intros.
assert( exists D1, exists D2, D=(D1,A);D2 ).
- apply elem_ctxsplit.
  assumption.
- destruct H0 as [D1'].
  destruct H0 as [D2'].
  rewrite H0.
  apply nd_vhyp.
Qed.

Hint Resolve nd_elem_vhyps.


(** Modal Axioms that characterized the logic S4 **)

(* Example 3.1 Axiom T is derivable in CS4 *)

Theorem Axiom_T: 
  forall (D G: ctx) (A:Formula), ND_Proof D G ((#A) ==> A).
Proof.
intros.
apply nd_intro.
eapply nd_boxE.
apply (nd_elem_thyps _ _ (#A)).
intuition.
intuition.
Qed.

Hint Resolve Axiom_T.

(* Example 3.2 Axiom 4 is derivable in CS4  *)
Theorem Axiom_4: 
  forall (D G: ctx) (A:Formula), ND_Proof D G (#A ==> ##A).
Proof.
intros.
apply nd_intro.
eapply nd_boxE. 
apply (nd_elem_thyps _ _ (#A)).
intuition.
intuition.
Qed.

Hint Resolve Axiom_4.


(* Example 3.3 Axiom K is derivable in CS4  *)
Theorem Axiom_K: 
  forall (D G: ctx) (A B:Formula),
  ND_Proof D G ((#(A ==> B)) ==> ((#A) ==> (#B))).
Proof.
intros.
repeat (apply nd_intro).
apply (nd_boxE D ((G, (# (A ==> B))), (# A)) A (#B)).
- intuition. 
- apply (nd_boxE _ _ (A ==> B) (#B)).
  * intuition.
  * apply nd_boxI.
    apply (nd_apply _ _ A B).
    + intuition. 
    + intuition.
Qed. 

Hint Resolve Axiom_K.

(* Proposition 3.9 Valid formulas are necessary truths *)
Proposition val_to_true: forall (D G:ctx) (A B:Formula),
    ND_Proof (D,A) G B -> ND_Proof D (G, #A) B.
Proof.
intros.
dependent induction H.
- auto.
- assert(K:=x); apply ctx_decomposition in x.
  destruct x.
  + destruct H.
    inversion H0.
    eapply nd_apply.
    * eapply Axiom_T.
    * intuition.
  + destruct H.
    rewrite H in K.
    simpl in K.
    inversion K.
    intuition.
- apply nd_intro.
  apply nd_exchange.
  assumption.
- eapply nd_apply.
  + exact IHND_Proof1.
  + exact IHND_Proof2. 
- apply (nd_boxE D (G,(#A)) (A) (#A0)).
  + intuition.
  + intuition.
- apply (nd_boxE D (G,(#A)) A C).
  + intuition.
  + change (G,(#A)) with (G;(empty,#A)).
    eapply (substitution).
    * exact H.
    * simpl.
      apply nd_weak_last.
      apply IHND_Proof2.
      reflexivity.
Qed.  

Hint Resolve val_to_true.



(* Definition 3.10 The boxed context*)
Fixpoint boxed (c:ctx) : ctx :=
  match c with
  | empty => empty
  | snoc G' b  => snoc (boxed G') (Box b)
  end.
  
Hint Unfold boxed.


(* Corollary 3.11 *)
Corollary ctx_val_to_true:
  forall (D G: ctx) (A: Formula),
  ND_Proof D G A -> ND_Proof empty (boxed D; G) A.
Proof.
intro.
induction D.
- auto.
- intros.
  simpl.
  apply val_to_true in H.
  apply IHD in H.
  apply ctx_exch_snoc.
  assumption.
Qed.

Hint Resolve ctx_val_to_true.


(* Corollary 3.12 Implication introduction for validity *)
Corollary nd_intro_val: forall (D G:ctx) (A B:Formula),
    ND_Proof (D,A) G B -> ND_Proof D G (#A ==> B).
Proof.
auto.
Qed.

Hint Resolve nd_intro_val.


Lemma nd_weakening_vhyps : 
  forall (D D': ctx) (G : ctx) (A : Formula),
  ND_Proof (D ; D') G A -> forall (B : Formula), ND_Proof (D, B ; D') G A.
Proof.
intros.
dependent induction H.
* apply nd_thyp.
* apply nd_elem_vhyps.
  assert(elem B (D;D')).
  rewrite <-x.
  intuition.
  apply elem_conc_split in H.
  destruct H.
  + apply elem_conc_L.
    intuition.
  + apply elem_conc_R. 
    assumption.
* apply nd_intro.
  apply IHND_Proof.
* eapply nd_apply.
  + apply IHND_Proof1; intuition.
  + apply IHND_Proof2; intuition.
* apply nd_boxI.
  apply IHND_Proof.
* eapply nd_boxE.
  + apply IHND_Proof1.
  + rewrite ctx_snoc_conc.
  apply IHND_Proof2. 
  reflexivity.
Qed.

Hint Resolve nd_weakening_vhyps.


Lemma nd_weak_lastV : 
  forall (D: ctx) (G: ctx) (A : Formula),
  ND_Proof D G A -> forall (B : Formula), ND_Proof (D, B) G A.
Proof.
intros.
assert (ND_Proof ((D,B);empty) G A); eauto.
Qed.

Hint Resolve nd_weak_lastV.


Lemma weakCtxV: 
  forall (D: ctx) (G : ctx) (A: Formula), 
  ND_Proof D G A -> forall (D': ctx), ND_Proof (D;D') G A.
Proof.
intros.
induction D'; auto.
assert (ND_Proof ((D;D'),f) G A); auto.
Qed.

Hint Resolve weakCtxV.


(* Proposition 3.13 Inversion of Implication introduction for validity*)
Lemma nd_intro_val_inv: forall (D G:ctx) (A B:Formula),
    ND_Proof D G (#A ==> B)  -> ND_Proof (D,A) G B.
Proof.
intros.
eapply nd_apply.
apply nd_weak_lastV.
exact H.
apply nd_boxI.
change (D,A) with ((D,A);empty).
apply nd_vhyp.
Qed.

Hint Resolve nd_intro_val_inv.


(* Proposition 3.14 Neccesary truths are valid  *)
Proposition true_to_val: forall (D G:ctx) (A B:Formula),
    ND_Proof D (G, #A) B -> ND_Proof (D,A) G B.
Proof.
intros.
apply nd_intro_val_inv.
apply nd_intro.
assumption.
Qed.

Hint Resolve true_to_val.


(* Corollary 3.15  *)
Corollary ctx_true_to_val:
  forall (D G: ctx) (A: Formula),
  ND_Proof empty (boxed D; G) A -> ND_Proof D G A.
Proof.
intro.
induction D.
- simpl.
  intros.
  rewrite (ctx_empty_conc G) in H.
  assumption.
- intros.
  simpl in H.
  apply nd_intro_gen in H.
  apply IHD in H.
  apply nd_intro_val_inv in H.
  assumption.
Qed.

Hint Resolve ctx_true_to_val.

Lemma boxed_conc:
forall (G G':ctx), boxed (G;G') = (boxed G);(boxed G').
Proof.
intros.
induction G'; auto.
simpl.
rewrite IHG'.
reflexivity.
Qed.

Hint Resolve boxed_conc.


