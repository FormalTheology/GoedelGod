(*** Chad E Brown, Andreas Teucke ***)
(*** Aug 2010 - June 2011 ***)

Require Export stt.

Lemma TImp : forall X Y:Prop , (X -> Y) -> (~X -> False) -> (Y -> False) -> False.
intros X Y H R1 R2.
apply R1. intros x. apply R2. apply (H x).
Qed.
Implicit Arguments TImp [X Y].

Lemma TNAnd : forall X Y:Prop , ~(X /\ Y) -> (~X -> False) -> (~Y -> False) -> False.
intros X Y H R1 R2. 
apply R1. intros x. apply R2. intro y. apply H. apply (conj x y).
Qed.
Implicit Arguments TNAnd [X Y].

Lemma TAnd : forall X Y:Prop , (X /\ Y) -> (X -> Y -> False) -> False.
intros X Y H R.
destruct H. apply R. apply H. apply H0.
Qed.
Implicit Arguments TAnd [X Y].

Lemma TOr : forall X Y:Prop , (X \/ Y) -> (X -> False) -> (Y-> False) -> False.
intros X Y H R R1. destruct H.
apply R. apply H. apply R1. apply H. 
Qed.
Implicit Arguments TOr [X Y].

Lemma TNor : forall X Y:Prop , ~(X \/ Y) -> (~X -> ~Y -> False) -> False.
intros X Y H R. apply R; intro h; apply H. left . apply h. right. apply h.
Qed.
Implicit Arguments TNor [X Y].

Lemma TNegImp : forall X Y:Prop , ~(X -> Y) -> (X -> ~Y -> False) -> False.
intros X Y H R.
apply H. intros x. destruct R.
apply x.
intros y. apply H. intros _. apply y.
Qed.
Implicit Arguments TNegImp [X Y].

Lemma TAll : forall (X : Type) (p:X -> Prop) , (forall x:X, p x) -> forall y:X, (p y -> False) -> False.
intros X p H y R.
apply R. apply H.
Qed.
Implicit Arguments TAll [X p].

Lemma TNegAll : forall (X : Type) (p:X -> Prop) , ~(forall x:X, p x) -> (forall y:X, ~p y -> False) -> False.
intros X p H R.
apply H. intros x. destruct (classic (p x)) as [a|a].
apply a.
destruct (R x a).
Qed.
Implicit Arguments TNegAll [X p].

Lemma TEx : forall (X : Type) (p:X -> Prop) , (exists x:X, p x) -> (forall y:X, p y -> False) -> False.
intros X p H R.
destruct H as [x H1].
apply (R x). apply H1.
Qed.
Implicit Arguments TEx [X p].

Lemma TNegEx : forall (X : Type) (p:X -> Prop) , ~(exists x:X, p x) -> forall y:X, (~p y -> False) -> False.
intros X p H y R. 
apply R. intro py. apply H.
exists y. apply py. 
Qed.
Implicit Arguments TNegEx [X p].

Lemma TBQ : forall X Y:Prop , (X = Y) -> (X -> Y -> False) -> ( ~X -> ~Y -> False) -> False.
intros X Y H .
rewrite H. intros H1 H2.
apply H2; intro y; apply H1; apply y.
Qed.
Implicit Arguments TBQ [X Y].

Lemma TBE : forall X Y:Prop , (X <> Y) -> (X -> ~Y -> False) -> ( ~X -> Y -> False) -> False.
intros X Y H R1 R2.
cut (~X); intro H0;cut (~Y); intro H1; 
apply H; apply prop_ext ; apply conj; auto. 
intro x. destruct (H0 x) .
intro y. destruct (H1 y) .
destruct R2; auto. destruct R1; auto. 
Qed.
Implicit Arguments TBE [X Y].

Lemma TIff : forall X Y:Prop , (X <-> Y) -> (X -> Y -> False) -> ( ~X -> ~Y -> False) -> False.
intros X Y H R1 R2.
destruct H. auto.
Qed.
Implicit Arguments TIff [X Y].

Lemma TNIff : forall X Y:Prop , ~(X <-> Y) -> (X -> ~Y -> False) -> ( ~X -> Y -> False) -> False.
intros X Y H R1 R2. 
cut (~X); intro H0;cut (~Y); intro H1; 
apply H; apply conj; auto. 
intro x. destruct (H0 x) .
intro y. destruct (H1 y) .
destruct R2; auto. destruct R1; auto. 
Qed.
Implicit Arguments TNIff [X Y].

Lemma TFQ : forall (Sig Tau: Type) (s t:Sig -> Tau) , 
(s = t) -> ((forall x:Sig, s x = t x) -> False) -> False.
intros Sig Tau s t H . rewrite H. intro R. apply R. intro x.
reflexivity.
Qed.
Implicit Arguments TFQ [Sig Tau s t].

Lemma TFE : forall (Sig Tau: Type) (s t:Sig -> Tau) , 
(s <> t) -> (~(forall x:Sig, s x = t x) -> False) -> False.
intros Sig Tau s t H R. apply R. intro . 
apply H. apply (functional_extensionality s t). apply H0.
Qed.
Implicit Arguments TFE [Sig Tau s t].

Lemma TCON : forall (Sig : Type) (s t u v:Sig) ,
 (s = t) -> (u <> v) -> 
( s <> u -> t <> u -> False) -> 
( s <> v -> t <> v -> False) -> False.
intros Sig s t u v [] H2 R1 R2.
apply R1; intro H3; destruct H3; 
apply R2; intro H3; destruct H3;
apply H2; reflexivity.
Qed.
Implicit Arguments TCON [Sig s t u v].

Lemma Ttrans : forall (Sig : Type) (s t u :Sig), 
(s=t) -> (t=u) -> ((s=u) -> False) -> False.
intros Sig s t u H1 H2 R1. apply R1. rewrite H1. apply H2.
Qed.
Implicit Arguments Ttrans [Sig s t u].

Lemma TDec : forall (Sig Tau: Type) (s t:Sig) (p q:Sig -> Tau),
p s <> q t -> (p <> q -> False) -> ( s <> t -> False) ->  False.
intros. apply H1. intro H2. destruct H2. apply H0. intro H2. destruct H2.
apply H. reflexivity. 
Qed.
Implicit Arguments TDec [Sig Tau s t p q].

Lemma TMat : forall (Sig : Type) (s t:Sig) (p q:Sig -> Prop),
p s -> ~ q t -> ( p <> q -> False ) -> ( s <> t -> False)-> False.
intros. apply H1. intros H3. destruct H3. apply H2. intros H3. destruct H3.
apply (H0 H). 
Qed.
Implicit Arguments TMat [Sig s t p q].

Lemma TSeps : forall (A:SType) (p:A->Prop) ,  ( p (Sepsilon p) -> False) -> forall x , ~ p x.
intros. intro px. apply H. apply Sepsilon_spec. exists x. apply px.
Qed.

Lemma TSeps' : forall (A:SType) (eps: (A->Prop)->A) (p:A->Prop) , (forall (q:A->Prop) (y:A), q y -> q (eps q)) -> (p (eps p) -> False) -> forall x , ~ p x.
intros. intro px. apply H0. refine (H _ x px).
Qed.

Lemma TSeps'' : forall (A:SType) (eps: (A->Prop)->A) (p:A->Prop) ,  (forall (q:A->Prop), ~ (forall (y:A),~ q y) -> q (eps q)) -> (p (eps p) -> False) -> forall x , ~ p x.
intros. intro px. apply H0. apply H. intro H1. apply (H1 x px).
Qed.

Lemma TSeps''' : forall (A:SType) (eps: (A->Prop)->A) (p:A->Prop) ,  (forall (q:A->Prop), (exists y:A , q y) -> q (eps q)) -> (p (eps p) -> False) -> forall x , ~ p x.
intros. intro px. apply H0. apply H. exists x. apply px.
Qed.

(*** Tactics to construct HO Proofs.  These correspond to tableau rules. ***)
Ltac tab_start H := (refine (NNPP _ _) ; intros H).
Ltac tab_dn H R:= (apply H ; intros R).
Ltac tab_false H := exact (FalseE _ H).
Ltac tab_refl H := (apply (H (refl_equal _))).
Ltac tab_conflict H H' := (exact (H' H) || exact (H' (sym_eq H)) ).

Ltac tab_imp H H1 := (apply (TImp H) ; intros H1).
Ltac tab_negimp H H1 H2 := (apply (TNegImp H) ; intros H1 H2).
Ltac tab_or H H1 := (apply (TOr H) ; intros H1).
Ltac tab_nor H H1 H2 := (apply (TNor H) ; intros H1 H2).
Ltac tab_nand H H1 := (apply (TNAnd H) ; intros H1).
Ltac tab_and H H1 H2 := (apply (TAnd H) ; intros H1 H2).

Ltac tab_inh S y := destruct (Sinh S) as [y].
Ltac tab_all H y H1 := (apply (TAll H y) ; intros H1).
Ltac tab_negall H y H1 := (apply (TNegAll H) ; intros y H1).
Ltac tab_negex H y H1 := (apply (TNegEx H y) ; intros H1).
Ltac tab_ex H y H1 := (apply (TEx H) ; intros y H1).

Ltac tab_dec' R := ((apply (TDec R); clear R;[ intro R; tab_dec' R | intro R] ) || (apply R; reflexivity)).
Ltac tab_dec H R := ((apply H; reflexivity) ||(apply (TDec H); [ intro R; tab_dec' R | intro R] ) ).
Ltac tab_mat H1 H2 R := (refine (TMat H1 H2 _ _);[ (intro R; tab_dec' R ) | intro R] ) || (refine (TMat H2 H1 _ _);[ (intro R; tab_dec' R ) | intro R] ).
Ltac tab_con H1 H2 R1 R2 := (apply (TCON H1 H2) ; intros R1 R2) ||  (apply (TCON H2 H1) ; intros R1 R2)  .

Ltac tab_trans H1 H2 R1 := ((refine (Ttrans H1 H2 _) ||refine (Ttrans (sym_eq H1) H2 _) ||refine (Ttrans H1 (sym_eq H2) _) ||refine (Ttrans (sym_eq H1) (sym_eq H2) _)); intro R1).

Ltac tab_be H H1 H2 := (apply (TBE H) ; intros H1 H2).
Ltac tab_bq H H1 H2 := (apply (TBQ H) ; intros H1 H2).
Ltac tab_negiff H H1 H2 := (apply (TNIff H) ; intros H1 H2).
Ltac tab_iff H H1 H2 := (apply (TIff H) ; intros H1 H2).

Ltac tab_fe H H1 := (apply (TFE H) ; intros H1).
Ltac tab_fq H H1 := (apply (TFQ H) ; intros H1).

Ltac tab_cut s R := (cut (~ s); intro R).  (*** (destruct (classic s) as [R|R]). ***)
Ltac tab_choice A p R := (cut (forall x, ~ p x);[intro R |  (apply (TSeps A p); intro R) ]).
Ltac tab_choice' A E p H R := (cut (forall x, ~ p x);[intro R | 
	 ((refine (TSeps' A E p H _) || refine (TSeps'' A E p H _) || refine (TSeps''' A E p H _)); intro R)
	]).
Ltac tab_rew_dn H R con := (generalize (eq_ind (fun x => ~ ~ x) (con) H (fun x => x) eq_neg_neg_id); intros R; simpl in R). (* ( change (con (fun x => ~ ~ x)) in H; rewrite eq_neg_neg_id in H; simpl in H). *)
Ltac tab_rew_true H R con := (generalize (eq_ind True (con) H (~ False) eq_true); intros R; simpl in R).
Ltac tab_rew_or H R con := (generalize (eq_ind or (con) H (fun (x y:Prop) => ~ x -> y) eq_or_imp); intros R; simpl in R).  (* ( change (con or) in H; rewrite eq_or_imp in H; simpl in H). *)
Ltac tab_rew_and H R con := (generalize (eq_ind and (con) H (fun (x y:Prop) => ~ (x -> ~ y)) eq_and_imp); intros R; simpl in R). (* ( change (con and) in H; rewrite eq_and_imp in H; simpl in H).*)
Ltac tab_rew_ex H R con := (generalize (eq_ind (fun p => exists x, p x) (con) H (fun p => ~forall x, ~p x) eq_exists_nforall); intros R; simpl in R). (* ( change (con (fun p x => exists x, p x)) in H; rewrite eq_exists_nforall in H; simpl in H).*)
Ltac tab_rew_eta H R con := (generalize (eq_ind (fun f x => f x) (con) H (fun f => f) eq_eta); intros R; simpl in R). (* ( change (con (fun f x => f x)) in H; rewrite eq_eta in H; simpl in H).*)
Ltac tab_rew_iff H R con := (generalize (eq_ind (fun (s:o) (t:o) => s <-> t) (con) H (fun (s:o) (t:o) => s = t) eq_iff); intros R; simpl in R). (* ( change (con (fun s t => s <-> t)) in H; rewrite eq_iff in H; simpl in H).*)
Ltac tab_rew_sym H R con := (generalize (eq_ind (fun s t => s = t) (con) H (fun s t => t = s) eq_sym_eq); intros R; simpl in R). (* ( change (con (fun s t => s = t)) in H; rewrite eq_sym_eq in H; simpl in H). *)
Ltac tab_rew_leib1 H R con := (generalize (eq_ind (fun s t => forall p: _ -> Prop, p s -> p t) (con) H (fun s t => s = t) eq_leib1); intros R; simpl in R). (* ( change (con (fun s t => forall p, p s -> p t)) in H; rewrite eq_leib1 in H; simpl in H).*)
Ltac tab_rew_leib2 H R con := (generalize (eq_ind (fun s t => forall p: _ -> Prop, ~ p s -> ~ p t) (con) H (fun s t => s = t) eq_leib2); intros R; simpl in R). (* ( change (con (fun s t => forall p, ~ p s -> ~ p t)) in H; rewrite eq_leib2 in H; simpl in H).*)
Ltac tab_rew_leib3 H R con := (generalize (eq_ind (fun s t => forall r: _ -> _ -> Prop, (forall x, r x x) -> r s t ) (con) H (fun s t => s = t) eq_leib3); intros R; simpl in R).  (* ( change (con (fun s t => forall r, (forall x, r x x) -> r s t )) in H; rewrite eq_leib3 in H; simpl in H).*)
Ltac tab_rew_leib4 H R con := (generalize (eq_ind (fun s t => forall r: _ -> _ -> Prop, ~ r s t -> ~(forall x, r x x) ) (con) H (fun s t => s = t) eq_leib4); intros R; simpl in R). (* ( change (con (fun s t => forall r, ~ r s t -> ~(forall x, r x x) )) in H; rewrite eq_leib4 in H; simpl in H).*)
