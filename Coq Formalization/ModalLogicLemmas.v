(* Formalization of Goedel's Ontological Proof of God's Existence *)

(* Authors: Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller *)


Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Pred_Type.


(* Type for worlds *)
Parameter i: Type.

(* Type for individuals *)
Parameter u: Type.

(* Type of lifted propositions *)
Definition o := i -> Prop.

(* Acessibility relation for worlds *)
Parameter r: i -> i -> Prop.



(* Modal connectives *)

Definition mnot (p: o)(w: i) := ~ (p w).
Notation "m~  p" := (mnot p) (at level 74, right associativity).

Definition mand (p: o)(q:o)(w: i) := (p w) /\ (q w).
Notation "p m/\ q" := (mand p q) (at level 79, right associativity).

Definition mimplies (p: o)(q:o)(w:i) := (p w) -> (q w).
Notation "p m-> q" := (mimplies p q) (at level 99, right associativity).

(* Modal quantifiers *)
Definition A {t: Type}(p: t -> o) := fun w => forall x, p x w.
Notation "A x \ p" := (A (fun x => p)) (at level 99, no associativity).
Definition E {t: Type}(p: t -> o) := fun w => exists x, p x w.


(* Modal operator for 'necessarily' *)
Definition box (p: o) := fun w => forall w1, (r w w1) -> (p w1).

(* Modal operator for 'possibly' *)
Definition dia (p: o) := fun w => exists w1, (r w w1) /\ (p w1).

(* Modal validity of lifted propositions *)
Definition V (p: o) := forall w, p w.



Lemma modus_ponens_inside_dia: V (A (fun p => A (fun q => (dia p) m-> (box (p m-> q)) m-> (dia q)))).
Proof.
intro.
intro p. intro q.
intro H1.
intro H2.
destruct H1 as [w1  [R1 H1]].
exists w1.
split.
  exact R1.

  apply H2. 
    exact R1.

    exact H1.
Qed.









(* Axioms for Modal Logic S5 *)

Axiom reflexivity: forall w, r w w.

Axiom transitivity: forall w1 w2 w3, (r w1 w2) -> (r w2 w3) -> (r w1 w3).

Axiom symmetry: forall w1 w2, (r w1 w2) -> (r w2 w1).


(* In modal logic S5, iterations of modal operators can be collapsed *)
Lemma modal_iteration: V (A (fun p => (dia (box p)) m-> (box p))).
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




(* Modal logic lemmas  *)

Lemma not_dia_box_not : V (A (fun p => (m~ (dia p)) m-> (box (m~ p)))).
Proof.
intro w.
intro p.
intro H1.
intros w1 R1.
apply not_ex_all_not with (n := w1) in H1.
apply not_and_or in H1.
destruct H1.
  contradiction.

  exact H.
Qed.

Lemma not_box_dia_not : V (A (fun p => (m~ (box p)) m-> (dia (m~ p)))).
Proof.
intro w.
intro p.
intro H1.
apply not_all_ex_not in H1.
destruct H1 as [w1 H1].
apply imply_to_and in H1.
destruct H1 as [H2 H3].
exists w1.
split.
  exact H2.

  exact H3.
Qed.




Lemma not_box_not__dia : V (A (fun p => (m~ (box (m~ p))) m-> (dia p))).
Proof.
intro w.
intro p.
intro H1.
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

Lemma Necessitation: forall p, (V p) -> (V (box p)).
Proof.
Admitted.

Lemma T: forall p w, ((box p) w) -> (p w).  (* check this *)
Proof.
Admitted.


Lemma Five: V (A (fun p => (dia p) m-> box (dia p))).
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
