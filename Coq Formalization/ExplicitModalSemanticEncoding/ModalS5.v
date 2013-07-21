(* Formalization of Goedel's Ontological Proof of God's Existence *)

(* Authors: Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller *)

Require Import Modal.

(* Axioms for Modal Logic S5 *)

Axiom reflexivity: forall w, r w w.

Axiom transitivity: forall w1 w2 w3, (r w1 w2) -> (r w2 w3) -> (r w1 w3).

Axiom symmetry: forall w1 w2, (r w1 w2) -> (r w2 w1).


(* In modal logic S5, iterations of modal operators can be collapsed *)
Lemma modal_iteration: V (mforall p, (dia (box p)) m-> (box p)).
Proof.
intro.
intro p.
intro H1.
destruct H1 as [w1 [R1 H1]].
intro. intro R0.
apply H1.
apply transitivity with (w2 := w).
  apply symmetry.
  exact R1.

  exact R0.
Qed.