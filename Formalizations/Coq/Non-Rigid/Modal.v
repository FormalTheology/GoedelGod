(* Embedding of Higher-Order Modal Logic into Classical Higher-Order Logic *)
(* Using non-rigid semantics *)

(* Authors: Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller *)

(* Type for worlds *)
Parameter i: Type.

(* Type for rigid individuals *)
Parameter v: Type.

(* Type for non-rigid individuals *)
Definition u := i -> v.



(* Type of lifted propositions *)
Definition o := i -> Prop.

(* Acessibility relation for worlds *)
Parameter r: i -> i -> Prop.


(* Modal connectives *)

(*Definition mequal {A: Type}(x y: A) := fun w: i => x = y.
Notation "x m= y" := (mequal x y) (at level 99, right associativity). *)

Definition mequal (x y: u) := fun w: i => x = y.
Notation "x m= y" := (mequal x y) (at level 99, right associativity).

Definition mnot (p: o)(w: i) := ~ (p w).
Notation "m~  p" := (mnot p) (at level 74, right associativity).

Definition mand (p q:o)(w: i) := (p w) /\ (q w).
Notation "p m/\ q" := (mand p q) (at level 79, right associativity).

Definition mor (p q:o)(w: i) := (p w) \/ (q w).
Notation "p m\/ q" := (mor p q) (at level 79, right associativity).

Definition mimplies (p q:o)(w:i) := (p w) -> (q w).
Notation "p m-> q" := (mimplies p q) (at level 99, right associativity).

Definition mequiv (p q:o)(w:i) := (p w) <-> (q w).
Notation "p m<-> q" := (mequiv p q) (at level 99, right associativity).


(* Modal quantifiers *)

Definition A {t: Type}(p: t -> o) := fun w => forall x, p x w.
Notation "'mforall'  x , p" := (A (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'mforall' x : t , p" := (A (fun x:t => p))
  (at level 200, x ident, right associativity, 
    format "'[' 'mforall' '/ '  x  :  t , '/ '  p ']'")
  : type_scope.


Definition E {t: Type}(p: t -> o) := fun w => exists x, p x w.
Notation "'mexists' x , p" := (E (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'mexists' x : t , p" := (E (fun x:t => p))
  (at level 200, x ident, right associativity, 
    format "'[' 'mexists' '/ '  x  :  t , '/ '  p ']'")
  : type_scope.


(* Modal operator for 'necessarily' *)
Definition box (p: o) := fun w => forall w1, (r w w1) -> (p w1).

(* Modal operator for 'possibly' *)
Definition dia (p: o) := fun w => exists w1, (r w w1) /\ (p w1).

(* Modal validity of lifted propositions *)
Definition V (p: o) := forall w, p w.
Notation "[ p ]" := (V p).
Ltac mv := match goal with [|- (V _)] => intro end.

(* Convenient tactics for modal operators *)

Ltac box_i := let w := fresh "w" in let R := fresh "R" in (intro w at top; intro R at top).

Ltac box_elim H w1 H1 := match type of H with 
                          ((box ?p) ?w) =>  cut (p w1); [intros H1 | (apply (H w1); try assumption) ]
                         end.

Ltac box_e H H1:= match goal with | [ |- (_ ?w) ] => box_elim H w H1 end.

Ltac dia_e H := let w := fresh "w" in let R := fresh "R" in (destruct H as [w [R H]]; move w at top; move R at top).

Ltac dia_i w := (exists w; split; [auto | idtac]).

Create HintDb modal.
Hint Unfold mequal mimplies mnot mor mand dia box A E V : modal.

Lemma mp_dia: [mforall p, mforall q, (dia p) m-> (box (p m-> q)) m-> (dia q)].
Proof. mv.
(* firstorder. *) (* This could solve the goal automatically *)
intros p q.
intros H1 H2.
dia_e H1.
dia_i w0.
box_e H2 H3.
apply H3.
exact H1.
Qed.

Lemma not_dia_box_not: [mforall p, (m~ (dia p)) m-> (box (m~ p))].
Proof. mv.
(* firstorder. *) (* This could solve the goal automatically *)
intro p.
intro H.
box_i.
intro H2.
apply H.
dia_i w0.
exact H2.
Qed.

Lemma box_not_not_dia: [ mforall p, (box (m~ p)) m-> (m~ (dia p)) ].
Proof. mv.
(* firstorder. *) (* This could solve the goal automatically *)
intro p.
intro H1.
intro H2.
dia_e H2.
box_elim H1 w0 H3.
apply H3.
exact H2.
Qed.

Lemma dia_not_not_box: [ mforall p, (dia (m~ p)) m-> (m~ (box p)) ].
Proof. mv.
(* firstorder. *) (* This could solve the goal automatically *)
intro p.
intro H1.
intro H2.
dia_e H1.
apply H1.
box_e H2 H3.
exact H3.
Qed.



(* Modal accessibility axioms *)

Axiom reflexivity: forall w, r w w.

Axiom transitivity: forall w1 w2 w3, (r w1 w2) -> (r w2 w3) -> (r w1 w3).

Axiom symmetry: forall w1 w2, (r w1 w2) -> (r w2 w1).



(* Modal axioms *)
(* Here we show how they can be derived from the accessibility axioms *)

Theorem K: [ mforall p, mforall q, (box (p m-> q)) m-> (box p) m-> (box q) ].
Proof.
(* firstorder. *) (* This could solve the goal automatically *)
mv.
intros p q.
intros H1 H2.
box_i.
box_e H1 H3. apply H3.
box_e H2 H4. exact H4.
Qed.


Theorem T: [ mforall p, (box p) m-> p ].
Proof.
(* firstorder using reflexivity. *) (* This could solve the goal automatically *)
mv.
intro p.
intro H.
box_e H H1. exact H1.
apply reflexivity. 
Qed. 

Theorem B: [ mforall p, (p m-> (box (dia p))) ].
Proof.
mv.
intro p.
intro H.
box_i.
dia_i w.
  apply symmetry.
  assumption.

  exact H.
Qed.
 

(* In strong modal logics, such as S5, iterations of modal operators can be collapsed *)
Theorem dia_box_to_box: [ mforall p, (dia (box p)) m-> (box p) ].
Proof.
(* firstorder using transitivity symmetry. *) (* This could solve the goal automatically *)
mv.
intro p.
intro H1.
dia_e H1.
box_i.
box_e H1 H2. exact H2.
eapply transitivity.
  apply symmetry.
  exact R.

  exact R0.
Qed.

