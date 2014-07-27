(* Formalization of Goedel's Ontological Proof of God's Existence *)

(* Authors: Bruno Woltzenlogel Paleo and Christoph Benzmueller *)


Require Import Coq.Logic.Classical.

Require Import Modal.

Ltac proof_by_contradiction H := apply NNPP; intro H.

(* Type of non-rigid unary properties *)
Definition property := i -> u -> o.

(* Constant predicate that distinguishes positive properties *)
(* Positivity is a rigid second-order property. It does not depend on worlds. *)
Parameter Positive: property -> o.

Definition property_neg(p: property) :=  fun w: i => (fun x: u => m~(p w x)) .


(* Axiom A1: either a property or its negation is positive, but not both *)
Axiom axiom1a : [ mforall p, (Positive (property_neg p)) m-> (m~ (Positive p)) ].
Axiom axiom1b : [ mforall p, (m~ (Positive p)) m-> (Positive (property_neg p)) ].


(* Axiom A2: a property necessarily implied by a positive property is positive *)
Axiom axiom2: forall w: i,( mforall p, mforall q, Positive p m/\ (fun w0: i => (forall w1, (r w w1) -> ((mforall x, (p w1 x) m-> (q w1 x) ) w1)) ) m-> Positive q ) w.


(* Theorem T1: positive properties are possibly exemplified *)
Theorem theorem1: forall w: i, ( mforall p, (Positive p) m-> (fun w0:i => exists w1, (r w0 w1) /\ ((mexists x, p w1 x) w1 ))) w.
Proof. 
intro w.
intro p.
intro H1.
proof_by_contradiction H2.
apply not_dia_box_not in H2.
unfold box in H2.
assert (H3: (fun w:i => (forall w1, (r w w1) -> (mforall x, m~ (p w1 x)) w1 )) w ). (* Lemma from Scott's notes *)
  box_i.
  intro x.
  assert (H4: ((m~ (mexists x : u, p w0 x)) w0)).
    apply (H2 w0 R).

    clear H2 R H1.
    intro H5.
    apply H4.
    exists x.
    exact H5.

  assert (H6: ((fun w0:i=> forall w1, (r w0 w1) -> ((mforall x, (p w1 x) m-> m~ (x m= x)) w1) ) w)). (* Lemma from Scott's notes *)    
    box_i.
    intro x.
    intros H7 H8.
    apply (H3 w0 R x).  (* box_elim H3 w0 G3. eapply G3. *)
    exact H7.

    assert (H9: ((Positive (fun w:i => (fun x => m~ (x m= x)) ) ) w)). (* Lemma from Scott's notes *)
      apply (axiom2 w p (fun w:i => (fun x => m~ (x m= x)))).
      split.
        exact H1.

        exact H6.

      assert (H10: ((fun w:i => forall w1, (r w w1) -> ((mforall x, (p w1 x) m-> (x m= x)) w1) ) w)). (* Lemma from Scott's notes *)
        box_i.
        intros x H11.
        reflexivity.

        assert (H11 : ((Positive (fun w:i => (fun x => (x m= x))) ) w)). (* Lemma from Scott's notes *)
          apply (axiom2 w p (fun w:i => (fun x => x m= x ) )).
          split.
            exact H1.

            exact H10.

          clear H1 H2 H3 H6 H10 p.
          apply axiom1a in H9.
          contradiction.
Qed.


(* Definition D1: God: a God-like being possesses all positive properties *)
Definition G(w: i)(x: u) := mforall p, (Positive p) m-> (p w x).


(* Axiom A3: the property of being God-like is positive *)
Axiom axiom3: [ Positive G ].


(* Corollary C1: possibly, God exists *)
Theorem corollary1: forall w:i, (fun w0:i => exists w1, (r w0 w1) /\ ((mexists x, G w1 x) w1) ) w .
Proof. intro.
apply theorem1.
apply axiom3.
Qed.


(* Axiom A4: positive properties are necessarily positive *)
Axiom axiom4: [ mforall p, (Positive p) m-> box (Positive p) ].


(* Definition D2: essence: an essence of an individual is a property possessed by it and necessarily implying any of its properties *)
Definition Essence(w: i)(p: property)(x: u) := 
  (p w x) m/\ mforall q: property, ((q w x) m-> (fun w0:i => forall w1, (r w0 w1) -> ((mforall y, (p w1 y) m-> (q w1 y)) w1) )).
Notation "p 'ess' x 'at' w" := (Essence w p x) (at level 69).


(* Theorem T2: being God-like is an essence of any God-like being *)
Theorem theorem2: forall w: i, ( mforall x, (G w x) m-> (G ess x at w) ) w.
Proof.
intros w.
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
Definition NE(w: i)(x: u) := mforall p, (p ess x at w) m-> (fun w0:i => forall w1, (r w0 w1) -> ((mexists y, (p w1 y)) w1) ).


(* Axiom A5: necessary existence is a positive property *)
Axiom axiom5: [ Positive NE ].


Lemma lemma1: forall w: i, (( (mexists z, (G w z)) m-> (fun w0:i => forall w1, (r w0 w1) -> ((mexists x, (G w1 x)) w1) ) ) w).
Proof.
intros w.
intro H1.
destruct H1 as [g H2].
cut ((G ess g at w) w).      (* Lemma from Scott's notes *)
  assert (H3: (NE w g w)).       (* Lemma from Scott's notes *)
    unfold G in H2.
    apply (H2 NE).
    apply axiom5.

    unfold NE in H3.
    intro H4.
    apply H3.
    exact H4.

  apply theorem2.
  exact H2.
Qed.


(* In strong modal logics, such as S5, iterations of modal operators can be collapsed *)
(*
Theorem dia_box_to_box_for_properties: forall w, (forall p: property, forall x: u, 
   (exists w1, (r w w1) /\ (forall w2, (r w1 w2) -> ((p w2 x) w2) )) -> 
   (forall w1, (r w w1) -> ((p w1 x) w1) ) ).
Proof.
firstorder using transitivity symmetry.
Qed. 
*)

(*
Lemma mp_dia_for_properties: forall w, forall p q: property, forall x: u,
               (exists w1, (r w w1) /\ ((p w1 x) w1)) -> 
               (forall w1, (r w w1) -> (((p w1 x) w1) -> ((q w1 x) w1))) ->
               (exists w1, (r w w1) /\ ((q w1 x) w1)).
Proof.
firstorder.
Qed.
*)

Lemma lemma2: forall w: i, (( fun w0:i => exists w1, (r w0 w1) /\ ((mexists z, (G w1 z)) w1) )  
                       m-> ( fun w0:i => forall w1, (r w0 w1) -> ((mexists x, (G w1 x)) w1) )) w.
Proof.
intro w.
intro H.
cut ((fun w0:i => exists w1, (r w0 w1) /\ 
       ((fun w0':i => forall w2, (r w0' w2) -> ((mexists x, G w2 x) w2 )) w1) ) w).  (* Lemma from Scott's notes *)
  firstorder using transitivity symmetry.

  firstorder using lemma1.
Qed.


(* Theorem T3: necessarily, a God exists *)
(* Theorem theorem3: forall w:i, (box (mexists x, (G w x)) ) w. *)
(* Theorem theorem3: forall w:i, (forall w1: i, (r w w1) -> (mexists x, (G w x)) ) w. *)
Theorem theorem3: forall w:i, (forall w1: i, (r w w1) -> ((mexists x, (G w1 x)) w1) ).
Proof.
intro w.
apply lemma2.
apply corollary1.
Qed.


Theorem T_for_properties: forall w, forall p: property,
                          (forall w1, (r w w1) -> exists x: u, ((p w1 x) w1))
                          ->
                          exists x: u, ((p w x) w).
Proof.
firstorder using reflexivity.
Qed.


(* Corollary C2: There exists a god *)
Theorem corollary2: forall w:i, ( mexists x, (G w x) ) w.
Proof.
intro w. apply T_for_properties. apply theorem3.
Qed.