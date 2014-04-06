(* Formalization of a variant of Goedel's Ontological Proof of God's Existence *)

(* Authors: Bruno Woltzenlogel Paleo, Annika Siders and Christoph Benzmueller *)

(* This variant differs from Scott's and Gödel's versions in the following aspects: 
     
     - The proof of theorem 1 is shorter. 
       Moreover, it uses axiom 2 only once and does not rely on equality.
       (this improved proof was found by Bruno)

     - Instead of proving theorem 3 using a strong iteration principle from S5
       and then proving corollary 2 from theorem 3 via axiom T, 
       corollary 2 is proved firstly and directly, using the weaker modal axiom B,
       and then theorem 3 follows trivially from corollary 2 by necessitation.
       (the fact that B is sufficient can be traced back at least to a work by André Fuhrmann, 
       and it has been discovered independently by Christoph and Bruno using automated provers.  
       The direct proof of corollary 2 using B was found by Annika)
*)

(* The numbering of axioms, definitions and theorems is exactly the same as in Scott's notes *)


Require Import Coq.Logic.Classical.

Require Import Modal.

Ltac proof_by_contradiction H := apply NNPP; intro H.


(* Constant predicate that distinguishes positive properties *)
Parameter Positive: (u -> o) -> o.


(* Axiom A1: either a property or its negation is positive, but not both *)
Axiom axiom1a : [ mforall p, (Positive (fun x: u => m~(p x))) m-> (m~ (Positive p)) ].
Axiom axiom1b : [ mforall p, (m~ (Positive p)) m-> (Positive (fun x: u => m~ (p x))) ].


(* Axiom A2: a property necessarily implied by a positive property is positive *)
Axiom axiom2: [ mforall p, mforall q, Positive p m/\ (box (mforall x, (p x) m-> (q x) )) m-> Positive q ].


(* Theorem T1: positive properties are possibly exemplified *)
Theorem theorem1: [ mforall p, (Positive p) m-> dia (mexists x, p x) ].
Proof. mv.
intro p.
intro H1.
proof_by_contradiction H2.
apply not_dia_box_not in H2.
assert (H3: ((box (mforall x, m~ (p x))) w)).
  box_i.
  intro x.
  assert (H4: ((m~ (mexists x : u, p x)) w0)).
    box_e H2 G2. 
    exact G2.

    clear H2 R H1 w.
    intro H5.
    apply H4.
    exists x.
    exact H5.

  assert (H6: ((box (mforall x, (p x) m-> m~ (p x))) w)).    
    box_i.
    intro x.
    intros H7 H8.
    box_elim H3 w0 G3.
    eapply G3.
    exact H7.

    assert (H9: ((Positive (fun x => m~ (p x))) w)).
      apply (axiom2 w p (fun x => m~ (p x))).
      split.
        exact H1.

        exact H6.

      apply axiom1a in H9.
      contradiction.
Qed.


(* Definition D1: God: a God-like being possesses all positive properties *)
Definition G(x: u) := mforall p, (Positive p) m-> (p x).


(* Axiom A3: the property of being God-like is positive *)
Axiom axiom3: [ Positive G ].


(* Corollary C1: possibly, God exists *)
Theorem corollary1: [ dia (mexists x, G x) ]. 
Proof. mv.
apply theorem1.
apply axiom3.
Qed.


(* Axiom A4: positive properties are necessarily positive *)
Axiom axiom4: [ mforall p, (Positive p) m-> box (Positive p) ].


(* Definition D2: essence: an essence of an individual is a property possessed by it and necessarily implying any of its properties *)
Definition Essence(p: u -> o)(x: u) := (p x) m/\ mforall q, ((q x) m-> box (mforall y, (p y) m-> (q y))).
Notation "p 'ess' x" := (Essence p x) (at level 69).


(* Theorem T2: being God-like is an essence of any God-like being *)
Theorem theorem2: [ mforall x, (G x) m-> (G ess x) ].
Proof. mv.
intro g.
intro H1.
unfold Essence.
split.
  exact H1.

  intro q.
  intro H2.
  assert (H3: ((Positive q) w)).
    proof_by_contradiction H4.
    unfold G in H1.
    apply axiom1b in H4.
    apply H1 in H4.
    contradiction. 

    cut (box (Positive q) w). (* Lemma from Scott's notes *)
      apply K.
      box_i.
      intro H5.
      intro y.
      intro H6.
      unfold G in H6.
      apply (H6 q).
      exact H5.

      apply axiom4.
      exact H3.
Qed.


(* Definition D3: necessary existence: necessary existence of an individual is the necessary exemplification of all its essences *)
Definition NE(x: u) := mforall p, (p ess x) m-> box (mexists y, (p y)).


(* Axiom A5: necessary existence is a positive property *)
Axiom axiom5: [ Positive NE ].


Lemma lemma1: [ (mexists z, (G z)) m-> box (mexists x, (G x)) ].
Proof. mv.
intro H1.
destruct H1 as [g H2].
cut ((G ess g) w).      (* Lemma from Scott's notes *)
  assert (H3: (NE g w)).       (* Lemma from Scott's notes *)
    unfold G in H2.
    apply (H2 NE).
    apply axiom5.

    unfold NE in H3.
    apply H3.

  apply theorem2.
  exact H2.
Qed.


(* Corollary C2: There exists a god *)
Theorem corollary2: [ mexists x, (G x) ].
Proof. mv.
apply NNPP.
assert (H: ((m~ (box  (dia (m~ mexists x, (G x) ) ) ) ) w) ).
  intro H1.
  assert (H2: ((dia (mexists x, (G x))) w)).
    apply corollary1.

    contradict H2.
    apply box_not_not_dia.
    box_i.
    cut ((m~ (box (mexists x : u, G x))) w0).
      intro H3.
      intro H4.
      apply H3.
      apply lemma1.
      exact H4.
    
      box_e H1 H5.
      apply dia_not_not_box.
      exact H5.

  intro H6.
  apply H.
  apply B.
  exact H6.      
Qed.


(* Theorem T3: necessarily, a God exists *)
Theorem theorem3: [ box (mexists x, (G x)) ].
Proof. mv.
box_i.
apply corollary2.
Qed.