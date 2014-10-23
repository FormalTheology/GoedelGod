
theory Hajek2002_Section5_var
imports Main "../QML_var"

begin

section {* Hajek's Small Emendations *}

text {* This is the theory called AOE'_0 in Definition 12 of Section 5 of Hajek (2002)  *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

text {* In item 2 of the summary in Page 14 of Hajek (2002),
        a different definition for G is written. Here it is assumed that
        this was a mistake. Definition 12 is assumed to be correct.  *}

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<equiv>  ( (\<box> (\<Phi> x ))) ))" 

  axiomatization where
    A12:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow>  (m\<not> (P (\<lambda>y.( m\<not> (\<Psi> y)) ) ) )   ))]" and
    A3:  "[P (\<lambda>x. (G x) m\<and> (eiw x) ) ]" 


subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Provability of A1 *}

text {* This appears as Lemma 3 in Section 4 of Hajek (2002) *} 

  theorem A1: "[\<forall>(\<lambda>\<Phi>. ((P \<Phi>) m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))) )  )]"
  by (metis A12)

subsection {* Counter-Satisfiability of old A3 *}

text {* The old A3 is not valid anymore. 
        This is counter-intuitive, because it shows that 
        a conjunct of a compound positive property is not necessarily positive.
        This contrasts with Hajek's claim that A12 and the new A3 
        "give a rather pleasant emendation of Gödel's axioms". *}

  theorem OldA3:  "[P G]" 
  nitpick [user_axioms] oops


subsection {* Independence of A2 *}

  theorem A2: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]"
  nitpick [user_axioms, expect = genuine]
  nitpick [satisfy, user_axioms, expect = genuine]
  oops


subsection {* Provability of T1, C1 and T3 *}
  
(* Satallax succeeds, but Leo2 and Metis fail. *)

  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists>e \<Phi>))]"
  sledgehammer [provers = remote_satallax remote_leo2, verbose] (A12)
  (* by (metis A12) *)
  sorry

  corollary C1: "[\<diamond> (\<exists>e G)]"
  (* sledgehammer [remote_satallax remote_leo2, verbose] (T1 A3) *)
  by (metis (no_types, lifting) A3 T1)

  lemma L1: "[\<forall>e(\<lambda>u.( (G u) m\<rightarrow> (\<box> ((G u) m\<and> (eiw u) ) ) ) ) ]"
  (* sledgehammer [remote_satallax remote_leo2, verbose] (G_def T1 C1 A12 A3 sym trans) *)
  by (metis (erased, lifting) A3 G_def)

  axiomatization where
    sym:   "x r y \<longrightarrow> y r x"
    
  theorem T3: "[\<box> (\<exists>e G)]"
  (* sledgehammer [provers = remote_satallax remote_leo2, verbose, timeout = 200] (L1 C1 T1 A12 A3 sym trans G_def) *)
  by (metis C1 L1 sym)


subsection {* Consistency again (now with sym) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms] oops


subsection {* Provability of A4 and A5 *}
  
  axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

(* Satallax succeeds, but Metis fails *)

  theorem A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 
  (* sledgehammer min [remote_satallax, verbose] (T3 A3 G_def sym trans) *)
  (* by (metis A3 G_def sym trans T3) *)
  sorry

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>e(\<lambda>y. \<Phi> y)))))"

  
(* Neither a proof nor a counter-model could be found for A5 *)

  theorem A5: "[P NE]"
  (* nitpick [user_axioms, verbose, timeout = 600] *)
  (* sledgehammer min [provers = remote_satallax remote_leo2, verbose, timeout=210] (T3 A3 T1 C1 L1 A12 ess_def NE_def G_def sym trans) *)
  (* by (metis A12 A3 ess_def NE_def) *)
  oops

end
