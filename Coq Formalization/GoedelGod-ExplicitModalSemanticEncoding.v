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


(* Modal logic axioms *)
Lemma Necessitation: forall p, (V p) -> (V (box p)).
Proof.
Admitted.

Lemma T: forall p w, ((box p) w) -> (p w).  (* check this *)
Proof.
Admitted.







(* Axiom 1: properties necessarily entailed by positive properties are also positive *)
Axiom axiom1: V (A (fun p => (A (fun q => Positive p m/\ (box (A (fun x: u => (p x) m-> (q x)))) m-> Positive q)))).



(* Axiom 2: the negation of a property is positive iff the property is not positive *)
Axiom axiom2a : V (A (fun p => (Positive (fun x: u => n (p x))) m-> (n (Positive p)))).
Axiom axiom2b : V (A (fun p => (n (Positive p)) m-> (Positive (fun x: u => n (p x))) )).





Axiom reflexivity: forall w, r w w.

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


(* ToDo: Everything below this point is garbage.. *)


(* Definition of God *)
Definition G(x: i) := forall p, (Positive p) -> (p x).

(* Axiom 3: Being God is a positive property *)
Axiom axiom3: (Positive G).

(* Theorem 2: it is possible that God exists *)
Theorem theorem2: diamond (exists x, G x). 
Proof.
apply theorem1.
apply axiom3.
Qed.


(* Definition of essentiality *)
Definition Essential(p: i-> Prop)(x: i) := (p x) /\ forall q: (u -> Prop),((q x) -> box (forall y, (p y) -> (q y))).

(* Axiom 4: positive properties are necessarily positive *)
Axiom axiom4: forall p, (Positive p) -> box (Positive p).

(* Theorem 3: if an individual is a God, then being God is an essential property for that individual *)
Theorem theorem3: forall y, (G y) -> (Essential G y).
Proof.
intro.
intro H1.
unfold Essential.
split.
  exact H1.

  intro.
  intro H2.
  cut (box (Positive q)).
    intro H3.
    apply Necessitation.
    cut (Positive q).
      intro H4.
      intro.
      intro H5.
      cut (Positive q).
        unfold G in H5.
        apply H5.

        exact H4.
     
      apply T.
      exact H3.

  cut (q y).
    intro H6.
    cut (Positive q).
      apply axiom4.

      cut (q y).
        intro H7.
        apply NNPP.
        intro not_Pos_q.
        absurd (q y).
          cut (Positive (fun x => ~ (q x))).
            unfold G in H1.
            apply H1.

            cut (~ (Positive q)).
              apply axiom2.

              exact not_Pos_q.

          exact H7.

        exact H6.

    exact H2.
Qed.


(* Definition of necessary existence *)
Definition NecExists(x: i) := forall p, (Essential p x) -> box (exists y, (p y)).

(* Axiom 5: necessary existence is a positive property *)
Axiom axiom5: (Positive NecExists).


(* The following lemma could be proved trivially (with intro and apply Necessitation). *)
(* The more complex proof below shows, however, that axiom Necessitation is not necessary if we use the definition of God *)
Lemma lemma: (exists z, (G z)) -> box (exists x, (G x)).
Proof.
intro H1.
destruct H1 as [g H2].
cut (Essential G g).
  cut (NecExists g).
    intro H3.
    unfold NecExists in H3.
    apply H3.

    cut (Positive NecExists).
      unfold G in H2.
      apply H2.

      apply axiom5.

  cut (G g).
    apply theorem3.

    exact H2.
Qed.


(* This lemma is not true. It should be (diamond p) -> (box (p -> q)) -> (diamond q) *)
Lemma modus_ponens_inside_diamond: forall p q: Prop, (diamond p) -> (p -> q) -> (diamond q).
(* ToDo: it might be possible to simplify the following proof *)
Proof.
intro. intro.
intro H1.
intro H2.
unfold diamond.
intro H3.
absurd q.
  apply T.
  exact H3.

  apply H2.
  apply imply_to_or in H2.
  destruct H2 as [H4|H5].
    unfold diamond in H1.
    apply Necessitation in H4.

    absurd (box (~ p)).
      exact H1.
      exact H4.

      apply T in H3.
      exfalso.
      contradiction.
Qed.



(* More modal logic axioms *)
Axiom Five: forall p, (diamond p) -> box (diamond p).

(* In modal logic S5, iterations of modal operators can be collapsed *)
Theorem modal_iteration_S5: forall p, (diamond (box p)) <-> (box p).
Proof.
Admitted. (* ToDo *)


(* Theorem 4: the existence of a God is necessary *)
Theorem theorem4: box (exists x, G x).
Proof.
cut (diamond (box (exists x, G x))).
  apply modal_iteration_S5.
  cut (diamond (exists x, G x)).
    intro H1.
    apply modus_ponens_inside_diamond with (p := exists z, G z).
    exact H1.
     
    apply lemma.

  apply theorem2.
Qed.


(* Theorem 5: There exists a god *)
Theorem God_exists: exists x, (G x).
Proof.
apply T.
apply theorem4.
Qed.

