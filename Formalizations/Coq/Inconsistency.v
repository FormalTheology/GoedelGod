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

