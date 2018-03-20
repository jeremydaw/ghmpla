(** Contexts and Properties *)
(** This module is for a general theory of contexts implemented as 
snoc lists where the focused element in the context is at the right-hand side.
 *)

Require Import Coq.Program.Equality.
Require Import ModalLogic.


Set Implicit Arguments.

(** Definition of Context of Formulae *)
Inductive ctx : Type :=
 | empty : ctx
 | snoc : ctx -> Formula -> ctx.

Notation " G , p " := (snoc G p) (at level 20, p at next level).


(* Definition of equality between contexts *)
Proposition eq_ctx_dec (G G': ctx): {G = G'} + {G <> G'}.
Proof.
intros.
decide equality.
Qed.

Hint Resolve eq_ctx_dec.


Proposition eq_ctx_dec_empty (G:ctx): {G=empty} + {G<>empty}.
Proof.
intros.
decide equality.
Qed.

Hint Resolve eq_ctx_dec_empty.


(************* CONTEXT OPERATIONS **************)

(* Context concatenation *)
Fixpoint conc (G G' : ctx) : ctx :=
  match G' with
  | empty => G
  | snoc D q => snoc (conc G D) q
  end.

Hint Unfold conc.

Notation " G ; D " := (conc G D) (at level 20).


Fixpoint elem (a:Formula) (G:ctx)  : Prop :=
  match G with
  | empty => False
  | G',b => b = a \/ elem a G'
  end.

Hint Unfold elem.


(*************CONTEXT PROPERTIES **************)

(*********** ABOUT ELEM ************)

Lemma elem_empty: 
  forall (A: Formula), ~ elem A empty.
Proof.
intros.
simpl.
unfold not.
trivial.
Qed.

Hint Resolve elem_empty.


Lemma elem_ctxhead:
  forall (A: Formula) (G: ctx), elem A (G,A).
Proof.
intros.
simpl.
left.
reflexivity.
Qed.

Hint Resolve elem_ctxhead.


Lemma elem_ctxcons:
  forall (A B: Formula) (G:ctx), elem B G -> elem B (G,A).
Proof.
intros.
simpl.
right.
trivial.
Qed.

Hint Resolve elem_ctxcons.


Lemma elem_mid:
  forall (A: Formula) (G G': ctx), elem A ((G,A);G').
Proof.
intros.
induction G'.
- simpl. left. reflexivity.
- assert(((G, A); (G', f)) = ((G, A); G'), f ).
  + simpl. reflexivity.
  + rewrite H. apply elem_ctxcons. assumption.
Qed.

Hint Resolve elem_mid.


Lemma elem_inv:
  forall (A B:Formula) (G:ctx), elem B (G,A) -> (A = B) \/ elem B G.
Proof.
intros.
inversion H.
- left. assumption.
- right. assumption.
Qed.

Hint Resolve elem_inv.


Lemma elem_ctxsplit:
  forall (A: Formula) (G: ctx), 
  elem A G -> exists G1, exists G2, G=(G1,A);G2.
Proof.
intros.
induction G.
- elim H.
- inversion H.
  + exists G.
    exists empty.
    rewrite H0.
    simpl. 
    trivial.
  + assert ( exists G1, exists G2, G = (G1, A); G2 ).
    -- apply IHG. assumption.
    -- destruct H1 as [G1'].
       destruct H1 as [G2'].
       exists G1'.
       exists (G2',f).
       simpl.
       rewrite H1.
       reflexivity.
Qed.

Hint Resolve elem_ctxsplit.


Lemma elem_conc_split: 
  forall (A:Formula) (G G':ctx), elem A (G;G') -> elem A G \/ elem A G'.
Proof.
intros.
induction G'; simpl in H.
- left; trivial.
- destruct H.
  + right.
    rewrite H.
    apply elem_ctxhead.
  + assert(elem A G \/ elem A G').
    -- apply IHG'. assumption.
    -- destruct H0.
       * left. assumption.
       * right. apply elem_ctxcons. assumption.
Qed.

Hint Resolve elem_conc_split.


Lemma elem_conc: 
  forall (A:Formula) (G G0 G1: ctx),  
  G=(G0;G1) -> elem A G -> elem A G0 \/ elem A G1.
Proof.
intros.
rewrite H in H0.
case (elem_conc_split A G0 G1).
+ assumption.
+ intro; left; trivial.
+ intro; right; trivial.
Qed.

Hint Resolve elem_conc.


Lemma elem_conc_L: 
  forall (A:Formula) (G:ctx), elem A G -> forall (G':ctx), elem A (G;G').
Proof.
intros.
induction G'.
- simpl. trivial.
- case (elem_conc_split A G G' IHG'); intros; simpl; right; assumption.
Qed.

Hint Resolve elem_conc_L.


Lemma elem_conc_R: 
  forall (A:Formula) (G' G:ctx), elem A G' -> elem A (G;G').
Proof.
intros A G'.
induction G'; intros.
- inversion H.
- simpl conc.
  inversion H; simpl.
  + left. exact H0.
  + right. apply IHG'. exact H0.
Qed.

Hint Resolve elem_conc_R.


Lemma elemSplit: 
  forall (G: ctx) (A B: Formula), B <> A -> elem B G -> 
  forall (G0 G0': ctx), G ~= (G0,A);G0' -> elem B (G0;G0').
Proof.
intros.
rewrite H1 in H0.
assert (elem B (G0,A) \/ elem B G0').
- apply elem_conc_split. assumption.
- destruct H2.
  + assert (A=B \/ elem B G0).
    -- apply elem_inv. assumption.
    -- destruct H3.
       * intuition.
       * apply elem_conc_L. assumption.
  + apply elem_conc_R. assumption.
Qed.

Hint Resolve elemSplit.


(*********** ABOUT CONC ************)

Proposition ctx_eq_snoc:
  forall (G G':ctx) (A:Formula), G = G' -> G,A = G',A.
Proof.
intros.
rewrite H.
reflexivity.
Qed.

Hint Resolve ctx_eq_snoc.


Proposition ctx_eq_snoc_cancell:
  forall (G G':ctx) (A:Formula), G,A = G',A -> G = G'.
Proof.
intros.
inversion H.
reflexivity.
Qed.

Hint Resolve ctx_eq_snoc_cancell.


Lemma ctx_eq_snoc_empty:
  forall (G : ctx) (A : Formula), (G,A) = ((G,A) ; empty).
Proof.
intros.
simpl.
reflexivity.
Qed.

Hint Resolve ctx_eq_snoc_empty.


Lemma ctx_eq_conc_empty:
  forall (G G': ctx), (G;G') = empty -> G = empty /\ G'= empty.
Proof.
intros.
destruct G; destruct G'; eauto.
- discriminate H.
- discriminate H.
Qed.

Hint Resolve ctx_eq_conc_empty.


Lemma ctx_empty_conc: 
  forall (G : ctx) , (empty;G) = G.
Proof.
intros.
induction G; simpl; eauto.
Qed.

Hint Resolve ctx_empty_conc.


Lemma ctx_conc_empty: 
  forall (G : ctx) , (G;empty) = G.
Proof.
intros.
induction G; simpl; eauto.
Qed.

Hint Resolve ctx_conc_empty.


Lemma ctx_snoc_conc:
  forall (G G': ctx) (A B: Formula), (((G,A);G'),B) = ((G,A);(G',B)).
Proof.
intros.
simpl.
reflexivity.
Qed.

Hint Resolve ctx_snoc_conc.


Lemma ctx_snoc_concbis :
  forall (G G': ctx) (A B: Formula), (((G,A),B);G')=((G,A);((empty,B);G')).
Proof.
intros.
induction G'; simpl; auto.
Qed.

Hint Resolve ctx_snoc_concbis.


Lemma ctx_conc_conc:
  forall (G G' G'' : ctx), G; (G';G'') = (G;G');G''.
Proof.
intros.
induction G''; simpl.
- reflexivity.
- rewrite IHG''. reflexivity.
Qed.

Hint Resolve ctx_conc_conc.


Lemma ctx_nempty_split:
  forall (G: ctx), G <> empty -> exists (G1 G2:ctx), G = G1;G2.
Proof.
intros.
induction G.
- exists empty. exists empty. simpl. reflexivity.
- case_eq G; intros.
  + exists empty. exists (empty,f). simpl. reflexivity.
  + rewrite H0 in IHG.
    destruct IHG.
    -- intuition. 
     apply H. discriminate H1.
    -- destruct H1.
       exists x.
       exists (x0,f).
       rewrite H1.
       simpl.
       reflexivity.
Qed.

Hint Resolve ctx_nempty_split.


Lemma ctx_inv_nonempty: forall (G:ctx), G <> empty -> 
        exists (G':ctx) (A:Formula), G = G',A.
Proof.
intros.
induction G.
intuition.
exists G.
exists f.
reflexivity.
Qed.

Hint Resolve ctx_inv_nonempty.


Lemma ctx_decomposition:
  forall (G D P: ctx) (A: Formula), 
  (G;D = P,A) -> (D= empty /\ G = P,A) \/ exists (G'':ctx), D=(G'',A).
Proof.
intros.
case_eq D; intro.
- left. intuition. rewrite H0 in H. simpl in H. assumption.
- intros .
  right. rewrite H0 in H. simpl in H.
  assert (f=A).
  + inversion H. reflexivity.
  + rewrite H1.
    exists c. reflexivity.
Qed.

Hint Resolve ctx_decomposition.
