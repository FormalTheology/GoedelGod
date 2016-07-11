Require Import Coq.Logic.Classical.

Require Import Modal.


Definition mFalse (w: i) := (mexists p: o, (p m/\ m~ p)) w.

Definition mTrivial (w: i) := (mforall p: o, (p m/\ m~ p)) w.



Theorem dia_box_false_leads_to_inconsistency_metalevel: [(dia (box mFalse))] -> [mFalse].
Proof. 
intro H.
intro w.
destruct (H w) as [w0 [R0 H0]].
destruct (H w0) as [w1 [R1 H1]].
box_elim H0 w1 HF.
unfold mFalse in HF.
destruct HF as [p [HF1 HF2]].
contradiction.
Qed.


Lemma mimplies_to_mnot: [mforall p:o, (p m-> mFalse) m-> (m~ p)].
Proof. mv. 
(* firstorder. *) (* This could solve the goal automatically *)
intro p.
intro H.
intro H0.
destruct (H H0) as [p0 [H1 H2]].
apply H2.
exact H1.
Qed.


Theorem dia_box_false_leads_to_inconsistency_objectlevel: [(dia (box mFalse))] -> [mFalse].
Proof.
intro H.
intro w.
exists (dia (dia mFalse)).  (* Critical Step *)
split.
  dia_e (H w).
  dia_e (H w0).
  dia_i w0.
  dia_i w1.
  box_e H0 H3.
  exact H3.

  apply box_not_not_dia.
  box_i.
  apply box_not_not_dia.
  box_i.
  apply mimplies_to_mnot.
  intro H4.
  exact H4.
Qed.

Require Import GoedelGod_Scott.

(* Goedel's Definition D2: essence: an essence of an individual is a property necessarily implying any of its properties *)
Definition EssenceGoedel(p: u -> o)(x: u) := mforall q, ((q x) m-> box (mforall y, (p y) m-> (q y))).
Notation "p 'essG' x" := (EssenceGoedel p x) (at level 69).

Definition empty := fun x: u => fun w: i => False.

Lemma EmptyEssence: [ mforall x, (empty essG x) ].
Proof. mv.
intro x.
unfold EssenceGoedel.
intro q.
intro H.
box_i.
intro y.
intro H1.
unfold empty in H1.
contradiction.
Qed.

(* Goedel's Definition D3: necessary existence: necessary existence of an individual is the necessary exemplification of all its essences *)
Definition NEG(x: u) := mforall p, (p essG x) m-> box (mexists y, (p y)).

(* Goedel's Axiom A5: necessary existence is a positive property *)
Axiom axiom5G: [ Positive NEG ].

Lemma NEG_possibly_exemplified: [ dia (mexists x, NEG x) ]. 
Proof. mv.
apply theorem1.
apply axiom5G.
Qed.


Lemma aux: [(mexists x, (NEG x)) m-> (box mFalse)].
Proof. mv.
intro H.
destruct H as [x H1].
unfold NEG in H1.
assert ((empty essG x
        m-> box
              (mexists y : u, empty y))
       w); [apply H1 | clear H1].
unfold empty in H. unfold mimplies in H.
assert (box (mexists _ : u, fun _ : i => False) w).
  apply H.
  apply EmptyEssence.

  clear H.
  box_i.
  box_e H0 H1.
  destruct H1 as [y H2].
  contradiction.
Qed.

Theorem inconsistency: [mFalse].
Proof.
apply dia_box_false_leads_to_inconsistency_metalevel.
mv.
assert ((dia (mexists x, NEG x)) w); [apply NEG_possibly_exemplified | idtac].
dia_e H.
dia_i w0.
apply aux.
apply H0.
Qed.