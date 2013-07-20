(* Formalization of Goedel's Ontological Proof of God's Existence *)

(* Authors: Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller *)



Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Pred_Type.


(* Type for individuals in the world *)
Parameter u: Type.

(* Type for worlds *)
Parameter i: Type.

Definition o := i -> Prop.

(* Acessibility relation for worlds *)
Parameter r: i -> i -> Prop.

(* Constant predicate that distinguishes positive properties *)
Parameter Positive: (u -> o) -> o.

(* Modal negation *)
Definition n (p: o)(w: i) := ~ (p w).

(* Constant for the modal operator for 'necessarily' *)
Definition box (p: o) := fun w => forall w1, (r w w1) -> (p w1).

(* Constant for the modal operator for 'possibly' *)
Definition diamond (p: o) := fun w => exists w1, (r w w1) /\ (p w1).

(* Modal quantification *)
Definition A {t: Type}(p: t -> o) := fun w => forall x, p x w.
Definition E {t: Type}(p: t -> o) := fun w => exists x, p x w.

Definition mand (p: o)(q:o)(w: i) := (p w) /\ (q w).
Notation "p m/\ q" := (mand p q) (at level 80, right associativity).

Definition mimplies (p: o)(q:o)(w:i) := (p w) -> (q w).
Notation "p m-> q" := (mimplies p q) (at level 90, right associativity).

(* Modal validity *)
Definition V (p: o) := forall w, p w.

Ltac modal_valid := unfold V; intro.
Ltac modal_intro := unfold A; intro.
Ltac diamond := unfold diamond.

Lemma n_diamond_box_n : V (A (fun p => (n (diamond p)) m-> (box (n p)))).
Proof.
modal_valid.
unfold A; intro p.
unfold mimplies; intro H1.
unfold box; intro w1. intro R1.
unfold n. unfold n in H1.
unfold diamond in H1.
apply not_ex_all_not with (n := w1) in H1.
apply not_and_or in H1.
destruct H1.
  contradiction.

  exact H.
Qed.


Lemma n_box_n__diamond : V (A (fun p => (n (box (n p))) m-> (diamond p))).
Proof.
modal_valid.
unfold A; intro p.
unfold mimplies; intro H1.
unfold n in H1.
unfold box in H1.
unfold diamond. 
apply not_all_ex_not in H1.
destruct H1 as [w1 H].
exists w1.
split.
  apply not_imply_elim in H.
  exact H.

  apply not_imply_elim2 in H.
  apply NNPP in H.
  exact H.
Qed.


(* Modal logic axioms 
Lemma Necessitation: forall p, (V p) -> (V (box p)).
Proof.
Admitted.

Lemma T: forall p w, ((box p) w) -> (p w).  (* check this *)
Proof.
Admitted.*)







(* Axiom 1: properties necessarily entailed by positive properties are also positive *)
Axiom axiom1: V (A (fun p => (A (fun q => Positive p m/\ (box (A (fun x: u => (p x) m-> (q x)))) m-> Positive q)))).



(* Axiom 2: the negation of a property is positive iff the property is not positive *)
Axiom axiom2a : V (A (fun p => (Positive (fun x: u => n (p x))) m-> (n (Positive p)))).
Axiom axiom2b : V (A (fun p => (n (Positive p)) m-> (Positive (fun x: u => n (p x))) )).







(* Theorem 1: positive properties possibly have a witness *)
Theorem theorem1: V (A (fun p: u -> o => (Positive p) m-> diamond (E (fun x => p x) ) )).
Proof.
modal_valid.
unfold A. intro p.
unfold mimplies.
cut ((Positive p w) /\ ((box (A (fun x => (n (p x))))) w) -> (n (Positive p)) w).
  intro H.
  intro H2.
  apply imply_to_or in H.
  destruct H.
    apply not_and_or in H.
    destruct H.
      contradiction.
    
      unfold diamond.
      unfold box in H.
      apply not_all_ex_not in H.
      destruct H as [w1  H3].
      exists w1.
      apply imply_to_and in H3.
      destruct H3 as [H31 H32].
      split.
        exact H31.

        unfold E.
        unfold A in H32.
        apply not_all_ex_not in H32.
        unfold n in H32.
        destruct H32 as [x H32].
        exists x.
        apply NNPP in H32.
        exact H32.

    unfold n in H.
    contradiction.

  intro H4. destruct H4 as [H41 H42].
  apply axiom2a.
  apply (axiom1 w p).
  unfold mand. split.
    exact H41.

    unfold box. intro. intro R1.
    unfold A. intro.
    unfold mimplies.
    intro W5.
    unfold n.
    intro H5.
    unfold A in H42. unfold box in H42.
    absurd (n (p x) w1).
      unfold n. intro. contradiction.

      apply H42.
      exact R1.
Qed.  





(* Definition of God *)
Definition G(x: u) := A (fun p => (Positive p) m-> (p x)).

(* Axiom 3: Being God is a positive property *)
Axiom axiom3: V (Positive G).

(* Theorem 2: it is possible that God exists *)
Theorem theorem2: V (diamond (E (fun x => G x))). 
Proof.
unfold V. intro. apply theorem1.
apply axiom3.
Qed.






(* Definition of essentiality *)
Definition Essential(p: u -> o)(x: u) := (p x) m/\ A (fun q: (u -> o) => ((q x) m-> box (A (fun y => (p y) m-> (q y))))).

(* Axiom 4: positive properties are necessarily positive *)
Axiom axiom4: V (A (fun p => (Positive p) m-> box (Positive p))).

(* Theorem 3: if an individual is a God, then being God is an essential property for that individual *)
Theorem theorem3: V (A (fun y => (G y) m-> (Essential G y))).
Proof.
modal_valid.
unfold A. intro y.
unfold mimplies. intro H1.
unfold Essential.
unfold mand; split.
  exact H1.

  red. intro q.
  red; intro H2.
  cut (box (Positive q) w).
    intro H3.
    red. intro. intro R1.
    red. intro y0.
    red.
    cut (Positive q w1). (* trying w0 *)
      intro H4.
      intro H5.
      cut (Positive q w1).
        unfold G in H5.
        red in H5. red in H5.
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
        intro not_Pos_q.
        absurd (q y w).
          cut (Positive (fun x => n (q x)) w).
            unfold G in H1.
            apply H1.

            cut (n (Positive q) w).
              apply axiom2b.

              red. exact not_Pos_q.

          exact H7.

        exact H6.

    exact H2.
Qed.






(* Definition of necessary existence *)
Definition NecExists(x: u) := A (fun p => (Essential p x) m-> box (E (fun y => (p y)))).

(* Axiom 5: necessary existence is a positive property *)
Axiom axiom5: V (Positive NecExists).



Lemma lemma: V ((E (fun z => (G z))) m-> box (E (fun x => (G x)))).
Proof.
modal_valid.
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


Lemma modus_ponens_inside_diamond: V (A (fun p => A (fun q => (diamond p) m-> (box (p m-> q)) m-> (diamond q)))).
Proof.
modal_valid.
intro p. intro q.
intro H1.
intro H2.
unfold diamond in H1.
destruct H1 as [w1  [R1 H1]].
exists w1.
split.
  exact R1.

  apply H2. 
    exact R1.

    exact H1.
Qed.



Axiom reflexivity: forall w, r w w.

Axiom transitivity: forall w1 w2 w3, (r w1 w2) -> (r w2 w3) -> (r w1 w3).

Axiom symmetry: forall w1 w2, (r w1 w2) -> (r w2 w1).


(* More modal logic axioms *)
Lemma Five: V (A (fun p => (diamond p) m-> box (diamond p))).
Proof.
intro.
intro p.
intro H1.
destruct H1 as [w1 [R1 H1]].
intros w2 R2.
exists w1.
split.
  apply transitivity with (w2 := w).
  apply symmetry.
    exact R2.

    exact R1.

  exact H1.
Qed.
  


(* In modal logic S5, iterations of modal operators can be collapsed *)
Lemma modal_iteration_S5: V (A (fun p => (diamond (box p)) m-> (box p))).
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
Qed. (* ToDo *)


(* Theorem 4: the existence of a God is necessary *)
Theorem theorem4: V (box (E (fun x => (G x)))).
Proof.
modal_valid.
cut (diamond (box (E (fun x => G x))) w).
  apply modal_iteration_S5.
  cut (diamond (E (fun x => G x)) w).
    intro H1.
    apply (modus_ponens_inside_diamond w (E (fun z => G z))).
    exact H1.
     
    
    intro. intro R1.
    apply lemma.

  apply theorem2.
Qed.




(* Theorem 5: There exists a god *)
Theorem God_exists: V (E (fun x => (G x))).
Proof.
modal_valid.
apply (theorem4 w).
apply reflexivity.
Qed.


