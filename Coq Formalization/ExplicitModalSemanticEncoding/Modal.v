(* Formalization of Goedel's Ontological Proof of God's Existence *)

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