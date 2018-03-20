(* Modal logic *)
(* Original development by Selene Linares  *)

(* Language: propositional modal logic
   Judgments: contexts and formulas
 *)

Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import ZArith.
Require Import Bool.

Open Scope Z_scope.


Set Implicit Arguments.



(************* SYNTAX OF MODAL FORMULAE *****************)

Inductive Formula : Type :=
  | Varp : N -> Formula
  | Impl : Formula -> Formula -> Formula
  | Box  : Formula -> Formula.


Notation "x ==> y"  := (Impl x y) (at level 55, right associativity).
Notation "# x" := (Box x) (at level 54, right associativity).


(* Definition of equality between Formulas *)
Proposition eq_p_dec (A B:Formula): {A = B} + {A <> B}.
Proof.
intros.
decide equality.
apply N_eq_dec.
Qed.

Hint Resolve eq_p_dec.