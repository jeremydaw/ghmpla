# nd-ax-nec

This is the repository corresponding to the article "The equivalence of natural deduction and axiomatic characterizations of necessity, a formal verification" submitted to the AiML2018 conference.

Abstract:
We present a proof of the equivalence between two deductive systems for intuitionistic necessity, namely the judgmental reconstruction given by Pfenning and Davies by means of a natural deduction approach that makes a distinction between valid and true formulas, and an axiomatic characterization inspired by Hakli and Negri’s system of derivations from assumptions
for modal logic K, a Hilbert-style formalism designed to ensure the validity of the deduction theorem. Both systems and the proof of their equivalence are formally verified using the state-of-the-art proof-assistant COQ . 
Throughout the paper, we give enough details to being able to understand the mechanized proofs in a straight and simple way. Moreover, we also mention some challenges, mainly related to the context implementation by lists, that arose during the
migration from usual rigorous mathematical proofs to strictly formal mechanized proofs.


In this repository you will find the formal verification of all the statements characterizing a natural deduction system and an axiomatic sytem for necessity of the above deduction systems together with the proof of equivalence and complementary developments.

You will need the Coq proof assistant version 8.6 or higher (avaliable at https://coq.inria.fr/)

To intereact with the files, a Makefile is provided.
The CoqProject is named *ModalLogicS4*.
