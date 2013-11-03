(* Additional theorems derivable from Goedel's axioms *)

(* Authors: Bruno Woltzenlogel Paleo and Christoph Benzmueller *)

Require Import Modal.

Require Import Coq.Logic.Classical.

Require Import GoedelGod_Scott.


(* Leibniz's Law of the identity of the indiscernibles *)
(* Despite its intuitive appeal, this law is controversial. *)
(* The main objection against this law is *) 
(* Max Black's symmetric universe counter-model. *)
Axiom leibniz_law: forall A: Type, (V (mforall x: A, (mforall y: A, (mforall p, (p x) m<-> (p y)) m-> x m= y ))).


(* God is flawless: God has no negative property. *)
Theorem flawlessness: (V (mforall p, mforall x, (G x) m-> (m~ (Positive p)) m-> (m~ (p x))  )).
Proof.
intro.
intros p x H1 H2.
intro H3.
apply axiom1b in H2.
unfold G in H1.
apply H1 in H2.
contradiction.
Qed.

(* There is only one god. *)
Theorem monotheism: (V (mforall x, mforall y, (G x) m-> (G y) m-> x m= y)).
Proof.
intros w x y H1 H2.
apply leibniz_law.
intro p.
assert (H3 : ((Positive p) m\/ (m~ (Positive p))) w).
  apply classic. 

  destruct H3 as [H4|H5].
    split; intro H6; [apply (H2 p) | apply (H1 p)]; apply H4.

    split; intro H7; [apply (flawlessness w p x H1) in H5 | apply (flawlessness w p y H2) in H5]; contradiction.
Qed.


(* Modal collapse: Everything that is the case, is so necessarily. *)
(* This theorem is due to Sobel and is currently the main criticism against Goedel's axioms. *)
Theorem modal_collapse: (V (mforall p, p m-> (box p))).
Proof.
(*ToDo*)
Admitted.
