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
destruct (H w) as [w0 [R0 H0]].
destruct (H w0) as [w1 [R1 H1]].
assert (mFalse w1). apply H0. apply R1.
unfold mFalse in H2.
destruct H2 as [p [H21 H22]].
unfold mFalse.
exists (dia (dia mFalse)).  (* Critical Step *)
split.
  dia_i w0.
  dia_i w1.
  unfold mFalse.
  exists p.
  split.
    exact H21.

    exact H22.

  apply box_not_not_dia.
  box_i.
  apply box_not_not_dia.
  box_i.
  apply mimplies_to_mnot.
  intro H3.
  exact H3.
Qed.





(* ============ Deprecated Stuff ============== *)


Lemma aux: forall w, (mFalse1 w) -> False.
Proof. firstorder. Qed.

Theorem dia_box_false1_leads_to_inconsistency2: [(dia (box mFalse1))] -> [mFalse1].
Proof.
intro H.
intro w.
unfold mFalse1.
exists (dia (box mFalse1)).
destruct (H w) as [w1 [R1 H1]].
split.
  dia_i w1.
  box_i.
  box_e H1 H2.
  exact H2.

  intro H3.
  apply (aux w).


destruct (H1 w) as [w1 [R2 H2]].
destruct (H1 w1) as [w2 [R3 H3]].
box_elim H2 w2 HF.
unfold mFalse in HF.
exact HF.
Qed.



Theorem dia_box_trivial_leads_to_inconsistency: (exists w: i, exists p: o, [(dia (box mTrivial))]) -> False.
Proof.
intro H.
destruct H as [w [p H1]].
destruct (H1 w) as [w1 [R2 H2]].
destruct (H1 w1) as [w2 [R3 H3]].
box_elim H2 w2 HF.
unfold mTrivial in HF.
destruct (HF p) as [HF1 HF2].
apply HF2.
exact HF1.
Qed.

(* ======================== *)


Theorem dia_box_false_leads_to_inconsistency: (exists w: i, [(dia (box mFalse))]) -> False.
Proof.
intro H.
destruct H as [w H1].
destruct (H1 w) as [w1 [R2 H2]].
destruct (H1 w1) as [w2 [R3 H3]].
box_elim H2 w2 HF.
unfold mFalse in HF.
exact HF.
Qed.


Theorem dia_box_false1_leads_to_inconsistency: (exists w: i, [(dia (box mFalse1))]) -> False.
Proof.
intro H.
destruct H as [w H1].
destruct (H1 w) as [w1 [R2 H2]].
destruct (H1 w1) as [w2 [R3 H3]].
box_elim H2 w2 HF.
unfold mFalse1 in HF.
destruct HF as [p [HF1 HF2]].
apply HF2.
exact HF1.
Qed.

Theorem dia_box_false1_leads_to_inconsistency2: [(dia (box mFalse1))] -> [mFalse1].
Proof.
intro H.
intro w.
unfold mFalse1.
exists (dia (dia mFalse1)).
destruct (H w) as [w1 [R1 H1]].
destruct (H w1) as [w2 [R2 H2]].
split.
  dia_i w1.
  dia_i w2.
  box_e H1 H3.
  exact H3.

  intro H3.
  apply (aux w).
  dia_e H3.
  dia_e H3.
  unfold mFalse1 in H3.
  destruct H3 as [p [H31 H32]]. (* Interesting ex-falso across boxes here. Should not be allowed. *)
  contradiction.
Qed.

