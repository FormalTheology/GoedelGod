Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import Modal.


Theorem not_dia_box_not: V (mforall p, ((m~ (dia p)) m-> (box (m~ p)) )).
Proof.
Admitted.