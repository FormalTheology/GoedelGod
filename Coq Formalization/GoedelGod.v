(* Author: Bruno Woltzenlogel Paleo (bruno@logic.at) *)

(* Formalization of Goedel's Ontological Proof of God's Existence *)

Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Pred_Type.


(* Type for individuals and objects in the world *)
Parameter i: Type.

(* Constant predicate that distinguishes positive properties *)
Parameter Positive: (i -> Prop) -> Prop.

(* Constant for the modal operator for 'necessarily' *)
Parameter box: Prop -> Prop.

(* Constant for the modal operator for 'possibly' *)
Definition diamond (p: Prop) := ~ (box (~ p)).

(* Modal logic axioms *)
(* ToDo: Necessitation cannot be naively encoded as an axiom *)
Axiom Necessitation: forall p: Prop, p -> (box p).
Axiom T: forall p: Prop, (box p) -> p.

(* Axiom 1: properties necessarily entailed by positive properties are also positive *)
Axiom axiom1: forall p q: i -> Prop, Positive p /\ (box (forall x,(p x) -> (q x))) -> Positive q.

(* Axiom 2: the negation of a property is positive iff the property is not positive *)
Axiom axiom2 : forall p: i -> Prop, Positive (fun x => ~ (p x)) <-> ~ (Positive p).

(* Theorem 1: positive properties possibly have a witness *)
Theorem theorem1: forall p: i -> Prop, (Positive p) -> diamond (exists x, p x ).
Proof.
intro.
intro H1.
unfold diamond.
intro H2.
absurd (Positive p).
  apply axiom2.
  apply axiom1 with (p := p).
  split.
    exact H1.
  
    apply Necessitation.
    intro.
    intro H3.
    apply T in H2.
    apply not_ex_all_not with (n := x) in H2.
    exact H2.
  exact H1.
Qed.


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
Definition Essential(p: i-> Prop)(x: i) := (p x) /\ forall q: (i -> Prop),((q x) -> box (forall y, (p y) -> (q y))).

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

