(* Embedding of Modal Logic in Coq *)

(* Authors: Bruno Woltzenlogel Paleo (bruno@logic.at) and Christoph Benzmueller *)


(* Type for worlds *)
Parameter i: Type.

(* Type for individuals *)
Parameter u: Type.

(* Type of lifted propositions *)
Definition o := i -> Prop.

(* Acessibility relation for worlds *)
Parameter r: i -> i -> Prop.


(* Modal connectives *)

Definition mequal {A: Type}(x y: A) := fun w: i => x = y.
Notation "x m= y" := (mequal x y) (at level 99, right associativity).

Definition mnot (p: o)(w: i) := ~ (p w).
Notation "m~  p" := (mnot p) (at level 74, right associativity).

Definition mand (p q:o)(w: i) := (p w) /\ (q w).
Notation "p m/\ q" := (mand p q) (at level 79, right associativity).

Definition mimplies (p q:o)(w:i) := (p w) -> (q w).
Notation "p m-> q" := (mimplies p q) (at level 99, right associativity).

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


(* Convenient tactics for modal operators *)

Ltac box_intro w H := intros w H.

Ltac box_elim H w1 R1 Hn := 
  let P := match type of H with
             (* forall w0:i, r ?w w0 -> ?p w0 => p *)
             ((box ?p) _) => p
           end
  in cut (P w1); [intros Hn | apply (H w1 R1)].

Ltac dia_elim H w R newH := destruct H as [w [R newH]].

Ltac dia_intro w := (exists w; split; [assumption | idtac]).



Lemma modus_ponens_inside_dia: V (mforall p, mforall q, (dia p) m-> (box (p m-> q)) m-> (dia q)).
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


(* Modal accessibility axioms *)

Axiom reflexivity: forall w, r w w.

Axiom transitivity: forall w1 w2 w3, (r w1 w2) -> (r w2 w3) -> (r w1 w3).

Axiom symmetry: forall w1 w2, (r w1 w2) -> (r w2 w1).



(* Modal axioms *)
(* Here we show how they can be derived from the accessibility axioms *)

Theorem K: (V (mforall p, mforall q, (box (p m-> q)) m-> ( (box p) m-> (box q) ) )).
Proof.
intros w p q.
intros H1 H2.
intros w1 R1.
apply H1.
  exact R1.

  apply H2.
  exact R1.
Qed.


Theorem T: (V (mforall p, (box p) m-> p)).
Proof.
intros w p.
intro H.
apply H.
apply reflexivity.
Qed.  




(* In strong modal logics, such as S5, iterations of modal operators can be collapsed *)
Theorem dia_box_to_box: V (mforall p, (dia (box p)) m-> (box p)).
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

