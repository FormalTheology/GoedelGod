(*** Chad E Brown, Andreas Teucke ***)
(*** Aug 2010 - June 2011 ***)

(*** Classical + Extensional + Choice ***)
Require Export Coq.Logic.ClassicalFacts.
Require Export Coq.Logic.Classical_Prop.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Logic.Epsilon.

Axiom prop_ext : prop_extensionality.
Implicit Arguments prop_ext [A B].

Theorem prop_deg : prop_degeneracy.
apply prop_ext_em_degen.  apply prop_ext. intros A. apply classic.
Qed.

(*** eq_ind_l is the same as eq_ind, but with three implicit arguments.
     Use eq_ind_l and eq_ind_r as Leibniz-style elimination and its symmetric version. ***)
Definition eq_ind_l (A : Type) (x : A) (P : A -> Prop) (u:P x) (y:A) (v:x = y) : P y := eq_ind x P u y v.
Implicit Arguments eq_ind_l [A x y].

(*** Two variants of transitivity of equality. ***)
Lemma eq_trans2 (A:Type) (x y z:A) : x = y -> z = y -> x = z.
intros H1 H2. rewrite H2. exact H1.
Qed.

Lemma eq_trans3 (A:Type) (x y z:A) : y = x -> y = z -> x = z.
intros H1 H2. rewrite <- H1. exact H2.
Qed.

(*** Logical Identities ***)
(*** Used to delete double negations ***)
Theorem eq_neg_neg_id : (fun x:Prop => ~~x) = (fun x:Prop => x).
apply functional_extensionality. intros x. apply prop_ext. split.
exact (NNPP x).
intros u v. exact (v u).
Qed.

Theorem eq_true : True = ~False.
apply prop_ext. intuition. Qed. 

Theorem eq_and_nor : and = (fun (x y:Prop) => ~(~x \/ ~y)).
apply functional_extensionality. intros x. apply functional_extensionality. intros y.
apply prop_ext. split. tauto.
intros u. destruct (classic x) as [v|v] ; destruct (classic y) as [w|w] ; tauto.
Qed.

Theorem eq_or_nand : or = (fun (x y:Prop) => ~(~x /\ ~y)).
apply functional_extensionality. intros x. apply functional_extensionality. intros y.
apply prop_ext. split. tauto.
intros u. destruct (classic x) as [v|v] ; destruct (classic y) as [w|w] ; tauto.
Qed.

Theorem eq_or_imp : or = (fun (x y:Prop) => ~ x -> y).
apply functional_extensionality. intros x. apply functional_extensionality. intros y.
apply prop_ext. split.
tauto.
intros u. destruct (classic x) as [v|v] ; destruct (classic y) as [w|w] ; tauto.
Qed.

Theorem eq_and_imp : and = (fun (x y:Prop) => ~ (x -> ~ y)).
apply functional_extensionality. intros x. apply functional_extensionality. intros y.
apply prop_ext. split.
tauto.
intros u.  split.
destruct (classic x) as [v|v] ; tauto.
destruct (classic y) as [w|w] ; tauto.
Qed.

Theorem eq_imp_or : (fun (x y:Prop) => (x -> y)) = (fun (x y:Prop) => (~x \/ y)).
apply functional_extensionality. intros x. apply functional_extensionality. intros y.
apply prop_ext. split. destruct (classic x) as [v|v] ; tauto. tauto.
Qed.

Theorem eq_iff : (fun s t => s <-> t) = (fun s t => s = t).
apply functional_extensionality. intros x. apply functional_extensionality. intros y.
apply prop_ext. split.  intro H. apply prop_ext. apply H. 
intro H. rewrite H. tauto. 
Qed.

Theorem eq_sym_eq : forall (sig : Type) , (fun (s t:sig) => s = t) = (fun (s t:sig) => t = s).
intro sig.
apply functional_extensionality. intros x. apply functional_extensionality. intros y.
apply prop_ext. split; apply sym_eq.  
Qed.
Implicit Arguments eq_sym_eq [sig].

Theorem eq_forall_nexists : forall (A : Type) , (fun (f:A -> Prop) => forall x, f x) = (fun (f:A -> Prop) => ~exists x, ~f x).
intros A. apply functional_extensionality. intros f. apply prop_ext. split.
intros u v.  destruct v as [x w].  exact (w (u x)).
intros u x.  apply NNPP. intros v. apply u. exists x. exact v.
Qed.
Implicit Arguments eq_forall_nexists [A].

Theorem eq_exists_nforall : forall (A : Type) , (fun (f:A -> Prop) => exists x, f x) = (fun (f:A -> Prop) => ~forall x, ~f x).
intros A. apply functional_extensionality. intros f. apply prop_ext. split.
intros u v. destruct u as [x w].  exact (v x w).
intros u.  apply NNPP.   intros v.  apply u.  intros x w.  apply v.  exists x. exact w.
Qed.
Implicit Arguments eq_exists_nforall [A].

Theorem eq_leib1 : forall (A : Type) , (fun (s t:A) => forall (p: A -> Prop), p s -> p t) = (fun (s t: A ) => s = t).
intros A. apply functional_extensionality. intros x. 
apply functional_extensionality. intros y. apply prop_ext. split.
intro H. apply H. reflexivity. intros [] p px. apply px. 
Qed.
Implicit Arguments eq_leib1 [A].

Theorem eq_leib2 : forall (A : Type) , (fun (s t:A) => forall (p: A -> Prop), ~ p s -> ~ p t) = (fun (s t: A ) => s = t).
intros A. apply functional_extensionality. intros x. 
apply functional_extensionality. intros y. apply prop_ext. split.
intro H. apply NNPP. apply (H (fun z => x <> z)). intro H1. apply H1. reflexivity.
intros [] p px. apply px.
Qed. 
Implicit Arguments eq_leib2 [A].

Theorem eq_leib3 : forall (A : Type) , (fun (s t:A) => forall (r: A -> A -> Prop), (forall x, r x x) -> r s t) = (fun (s t: A ) => s = t).
intros A. apply functional_extensionality. intros x. 
apply functional_extensionality. intros y. apply prop_ext. split.
intro H. apply H. tauto.
intros [] p px. apply px.
Qed. 
Implicit Arguments eq_leib3 [A].

Theorem eq_leib4 : forall (A : Type) , (fun (s t:A) => forall (r: A -> A -> Prop),~ r s t -> ~ (forall x, r x x) ) = (fun (s t: A ) => s = t).
intros A. apply functional_extensionality. intros x. 
apply functional_extensionality. intros y. apply prop_ext. split.
intro H. apply NNPP. intro H1. apply (H (fun s t => s = t)). apply H1.
intro . reflexivity.
intros [] p px. intro H. apply px. apply H.
Qed. 
Implicit Arguments eq_leib4 [A].

(*** eta ***)
Theorem eq_eta : forall (A B: Type) , (fun (f:A -> B) (x:A) => f x) = (fun (f:A -> B) => f).
intros A B. apply functional_extensionality. intros f. apply functional_extensionality. intros x.
reflexivity.
Qed.
Implicit Arguments eq_eta [A B].

(*** Simple types as inhabited types, with coercion so they can be treated as ordinary types. ***)
Record SType : Type := mk_SType {
 Scarrier :> Type;                           (*** Coercion ***)
 Sinh : inhabited Scarrier               (*** inhabitation assumption ***)
}.

Theorem Prop_inh :inhabited Prop.
exact (inhabits True).
Qed.

Definition o := mk_SType Prop Prop_inh.

Theorem Sar_inh : forall (A B:SType) , inhabited (A -> B).
intros A B.
destruct (Sinh B) as [y].
exact (inhabits (fun _ => y)).
Qed.

Definition Sar (A B:SType) := mk_SType (A -> B) (Sar_inh A B).
Notation "A --> B" := (Sar A B) (at level 70, right associativity).

Theorem FalseE : forall P:Prop, False -> P.
intros P u. elim u.
Qed.

Theorem SinhE : forall (P:Prop) (A:SType) , (forall x:A, P) -> P.
intros P A u. destruct (Sinh A) as [x]. exact (u x).
Qed.
Implicit Arguments SinhE [P].

Definition Sepsilon {A : SType} : ((A --> o) --> A)
   := (fun P => (epsilon (Sinh A) P)).

Definition Sepsilon_spec {A : SType} : forall P:A -> Prop, (exists x, P x) -> P (Sepsilon P)
   := (fun P => (epsilon_spec (Sinh A) P)).

Definition Snot : o --> o := not.
Definition Sand : o --> o --> o := and.
Definition Sor  : o --> o --> o := or.
Definition Siff : o --> o --> o := iff.
Definition Seq (A:SType) : A --> A --> o := (@eq A).
Definition SPi (A:SType) : (A --> o) --> o := (fun p => forall x, p x).
Definition SSigma (A:SType) : (A --> o) --> o := (fun p => exists x, p x).

Theorem eq_forall_Seps {A : SType} (p:A --> o) : (forall x:A, p x) = p (Sepsilon (fun x => ~p x)).
apply prop_ext; split.
intros H1. apply H1.
intros H1. destruct (classic (exists x:A, ~p x)) as [H2|H2].
destruct (Sepsilon_spec (fun x => ~ p x)). exact H2. exact H1.
intros x. apply NNPP. intros H3. apply H2. exists x. exact H3.
Qed.

Theorem eq_SPi_Seps {A : SType} : SPi A = (fun p:A --> o => p (Sepsilon (fun x => ~p x))).
apply (functional_extensionality (SPi A)). intros p. apply eq_forall_Seps.
Qed.

Theorem eq_exists_Seps {A : SType} (p:A --> o) : (exists x:A, p x) = p (Sepsilon p).
apply prop_ext; split.
apply Sepsilon_spec.
intros H1. exists (Sepsilon p). exact H1.
Qed.

Theorem eq_SSigma_Seps {A : SType} : SSigma A = (fun p:A --> o => p (Sepsilon p)).
apply (functional_extensionality (SSigma A)). intros p. apply eq_exists_Seps.
Qed.

(***
 Simple Types (sigma,tau) ::= o | alpha | sigma --> tau
 HO Terms (s,t) ::= x | fun x [:sigma] => s | s t 
                      | forall x [:sigma], s | s -> t | not s | and s t | or s t | iff s t
                      | True | False
                      | Snot | Sand | Sor | Siff
                      | exists x [:sigma], s | s = t
                      | @Seq sigma | Seq s
                      | @Sepsilon sigma | Sepsilon s
                      | @SPi sigma | SPi s
                      | @SSigma sigma | SSigma s
 HO Proofs (D,E) ::= u | fun x [:sigma] => D | fun u [:s] => D
                       | D s | D E
                       | I | FalseE s D
                       | conj D E | proj1 D | proj2 D | and_ind D E
                       | or_introl s D | or_intror s D | or_ind E1 E2 D
                       | ex_intro t s D | ex_ind D E
                       | refl_equal s | eq_ind_l D E | eq_ind_r D E
                       | SinhE sigma D                     (*** Simple Types are Inhabited ***)
                       | classic s | NNPP s                (*** Classical ***)
                       | prop_ext D                        (*** BE ***)
                       | functional_extensionality s t D   (*** FE ***)
                       | Sepsilon_spec s D                 (*** Choice ***)
                                                           (*** Logical Identities and eta, useful especially for preprocessing
                                                                  a problem into a special form. ***)
                       | eq_neg_neg_id                     (*** ~ o ~ = id ***)
                       | eq_and_nor                        (*** and = \x y.~(~x \/ ~y) ***)
                       | eq_or_nand                        (*** or = \x y.~(~x /\ ~y) ***)
                       | eq_or_imp                         (*** or = \x y.~x -> y ***)
                       | eq_and_imp                        (*** and = \x y.~(x -> ~y) ***)
                       | eq_imp_or                         (*** (\x y.x -> y) = (\x y.~x \/ y) ***)
                       | eq_forall_nexists sigma           (*** (\f.forall x,f x) = (\f.~exists x,~f x) ***)
                       | eq_exists_nforall sigma           (*** (\f.exists x,f x) = (\f.~forall x,~f x) ***)
                       | eq_eta sigma tau                  (*** (\f:sigma --> tau (\x.f x)) = \f.f ***)
 ***)

