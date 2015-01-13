(* Formalization of Goedel's Ontological Proof of God's Existence *)

(* Authors: Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller *)


Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import Modal.


(* Constant predicate that distinguishes positive properties *)
Parameter Positive: (u -> o) -> o.


(* Axiom A1: either a property or its negation is positive, but not both *)
Axiom axiom1a : V (mforall p, (Positive (fun x: u => m~(p x))) m-> (m~ (Positive p))).
Axiom axiom1b : V (mforall p, (m~ (Positive p)) m-> (Positive (fun x: u => m~ (p x))) ).


(* Axiom A2: a property necessarily implied by a positive property is positive *)
Axiom axiom2: V (mforall p, mforall q, Positive p m/\ (box (mforall x, (p x) m-> (q x) )) m-> Positive q).


(* Theorem T1: positive properties are possibly exemplified *)
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
  apply axiom1a.
  apply (axiom2 w p).
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

(* Definition D1: God: a God-like being possesses all positive properties *)
Definition G(x: u) := mforall p, (Positive p) m-> (p x).

(* Axiom A3: the property of being God-like is positive *)
Axiom axiom3: V (Positive G).

(* Corollary C1: possibly, God exists *)
Theorem corollary1: V (dia (mexists x, G x)). 
Proof.
intro w. 
apply theorem1.
apply axiom3.
Qed.


(* Axiom A4: positive properties are necessarily positive *)
Axiom axiom4: V (mforall p, (Positive p) m-> box (Positive p)).

(* Definition D2: essence: an essence of an individual is a property possessed by it and necessarily implying any of its properties *)
Definition Essence(p: u -> o)(x: u) := (p x) m/\ mforall q, ((q x) m-> box (mforall y, (p y) m-> (q y))).
Notation "p 'ess' x" := (Essence p x) (at level 69).

(* Theorem T2: being God-like is an essence of any God-like being *)
Theorem theorem2: V (mforall x, (G x) m-> (G ess x)).
Proof.
intro.
intro y.
intro H1.
unfold Essence.
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
     
      apply H3. (* Box elimination *)
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
              apply axiom1b.

              exact H8.

          exact H7.

        exact H6.

    exact H2.
Qed.


(* Definition D3: necessary existence: necessary existence of an individual is the necessary exemplification of all its essences *)
Definition NE(x: u) := mforall p, (p ess x) m-> box (mexists y, (p y)).

(* Axiom A5: necessary existence is a positive property *)
Axiom axiom5: V (Positive NE).


Lemma lemma: V ((mexists z, (G z)) m-> box (mexists x, (G x))).
Proof.
intro w.
intro H1.
destruct H1 as [g H2].
cut ((G ess g) w).
  cut (NE g w).
    intro H3.
    unfold NE in H3.
    apply H3.

    cut (Positive NE w).
      unfold G in H2.
      apply H2.

      apply axiom5.

  cut (G g w).
    apply theorem2.

    exact H2.
Qed.


(* ToDo: According to experiments with LEO-II, modal logic KB should suffice for showing T3. There is no need to import S5 *)
Require Import Modal.

(* Theorem T3: necessarily, God exists *)
Theorem theorem3: V (box (mexists x, (G x))).
Proof.
intro.
cut (dia (box (mexists x, G x)) w).
  apply dia_box_to_box.
  cut (dia (mexists x, G x) w).
    intro H1.
    apply (mp_dia w (mexists z, G z)).
    exact H1.
     
    
    intro. intro R1.
    apply lemma.

  apply corollary1.
Qed.


(* Corollary C2: There exists a god *)
Theorem corollary2: V (mexists x, (G x)).
Proof.
intro.
apply (theorem3 w).
apply reflexivity.
Qed.
