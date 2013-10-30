Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import Modal.


Theorem not_dia_box_not: V (mforall p, ((m~ (dia p)) m-> (box (m~ p)) )).
Proof.
intro.
intro p.
intro H.
intros w1 H1.
intro H2.
apply H.
exists w1; split. exact H1.
exact H2.
Qed.

