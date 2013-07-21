(* Formalization of Goedel's Ontological Proof of God's Existence *)

(* Authors: Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller *)


Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import Modal.


(* Constant predicate that distinguishes positive properties *)
Parameter Positive: (u -> o) -> o.

(* Axiom 1: properties necessarily entailed by positive properties are also positive *)
Axiom axiom1: V (mforall p, mforall q, Positive p m/\ (box (A (fun x: u => (p x) m-> (q x)))) m-> Positive q).


(* Axiom 2: the negation of a property is positive iff the property is not positive *)
Axiom axiom2a : V (mforall p, (Positive (fun x: u => m~(p x))) m-> (m~ (Positive p))).
Axiom axiom2b : V (mforall p, (m~ (Positive p)) m-> (Positive (fun x: u => m~ (p x))) ).


(* Theorem 1: positive properties possibly have a witness *)
Theorem theorem1: V (mforall p, (Positive p) m-> dia (mexists x, p x) ).
Proof.
intro w.
intro p.
cut ((Positive p w) /\ ((box (mforall x, (m~ (p x)))) w) -> (m~ (Positive p)) w).
  intro H.
  intro H2.
  apply imply_to_or in H.
  destruct H.
    apply not_and_or in H.
    destruct H.
      contradiction.
    
      apply not_all_ex_not in H.
      destruct H as [w1  H3].
      exists w1.
      apply imply_to_and in H3.
      destruct H3 as [H31 H32].
      split.
        exact H31.

        apply not_all_ex_not in H32.
        destruct H32 as [x H32].
        exists x.
        apply NNPP in H32.
        exact H32.

    contradiction.

  intro H4. 
  destruct H4 as [H41 H42].
  apply axiom2a.
  apply (axiom1 w p).
  split.
    exact H41.

    intros w1 R1.
    intro x.
    intro W5.
    intro H5.
    absurd ((m~ (p x)) w1).
      intro H6. 
      contradiction.

      apply H42.
      exact R1.
Qed.  

(* Definition of God *)
Definition G(x: u) := mforall p, (Positive p) m-> (p x).

(* Axiom 3: Being God is a positive property *)
Axiom axiom3: V (Positive G).

(* Theorem 2: it is possible that God exists *)
Theorem theorem2: V (dia (mexists x, G x)). 
Proof.
intro w. 
apply theorem1.
apply axiom3.
Qed.

(* Definition of essentiality *)
Definition Essential(p: u -> o)(x: u) := (p x) m/\ mforall q, ((q x) m-> box (mforall y, (p y) m-> (q y))).

(* Axiom 4: positive properties are necessarily positive *)
Axiom axiom4: V (mforall p, (Positive p) m-> box (Positive p)).

(* Theorem 3: if an individual is a God, then being God is an essential property for that individual *)
Theorem theorem3: V (mforall y, (G y) m-> (Essential G y)).
Proof.
intro.
intro y.
intro H1.
unfold Essential.
split.
  exact H1.

  intro q.
  intro H2.
  cut (box (Positive q) w).
    intro H3.
    intros w1 R1.
    intro y0.
    cut (Positive q w1).
      intro H4.
      intro H5.
      cut (Positive q w1).
        unfold G in H5.
        apply H5.

        exact H4.
     
      apply H3.
      exact R1.

  cut (q y w).
    intro H6.
    cut (Positive q w).
      apply axiom4.

      cut (q y w).
        intro H7.
        apply NNPP.
        intro H8.
        absurd (q y w).
          cut (Positive (fun x => m~ (q x)) w).
            unfold G in H1.
            apply H1.

            cut ((m~ (Positive q)) w).
              apply axiom2b.

              exact H8.

          exact H7.

        exact H6.

    exact H2.
Qed.


(* Definition of necessary existence *)
Definition NecExists(x: u) := mforall p, (Essential p x) m-> box (mexists y, (p y)).

(* Axiom 5: necessary existence is a positive property *)
Axiom axiom5: V (Positive NecExists).


Lemma lemma: V ((mexists z, (G z)) m-> box (mexists x, (G x))).
Proof.
intro w.
intro H1.
destruct H1 as [g H2].
cut (Essential G g w).
  cut (NecExists g w).
    intro H3.
    unfold NecExists in H3.
    apply H3.

    cut (Positive NecExists w).
      unfold G in H2.
      apply H2.

      apply axiom5.

  cut (G g w).
    apply theorem3.

    exact H2.
Qed.



Require Import ModalS5.

(* Theorem 4: the existence of a God is necessary *)
Theorem theorem4: V (box (mexists x, (G x))).
Proof.
intro.
cut (dia (box (mexists x, G x)) w).
  apply modal_iteration.
  cut (dia (mexists x, G x) w).
    intro H1.
    apply (modus_ponens_inside_dia w (mexists z, G z)).
    exact H1.
     
    
    intro. intro R1.
    apply lemma.

  apply theorem2.
Qed.


(* Theorem 5: There exists a god *)
Theorem God_exists: V (mexists x, (G x)).
Proof.
intro.
apply (theorem4 w).
apply reflexivity.
Qed.
