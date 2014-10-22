
theory Hajek2002_Section4_var
imports Main "../QML_var"

begin

section {* Hajek's Small Emendations *}

text {* This is the theory called AOE' in Section 4 of Hajek (2002)  *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. (\<box> (\<Phi> x ))  m\<equiv>  ( \<exists>(\<lambda>\<Psi>.( (P \<Psi>) m\<and> (\<box> (\<forall>e(\<lambda>x. \<Psi> x m\<rightarrow> \<Phi> x))) )))  ))" 

  axiomatization where
    A12:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow>  (m\<not> (P (\<lambda>y.( m\<not> (\<Psi> y)) ) ) )   ))]" and
    A3:  "[P G]" 


subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Provability of A1 *}

text {* This appears as Lemma 3.1 in Section 4 of Hajek (2002) *} 

  theorem A1: "[\<forall>(\<lambda>\<Phi>. ((P \<Phi>) m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))) )  )]"
  by (metis A12)


subsection {* Counter-Satisfiability of A2 *}

  theorem A2: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]"
  nitpick [user_axioms, expect = genuine] oops


subsection {* Provability of T1, L1 and C1 *}

text {* T1 and L1 appear as Lemmas 3.2 and 3.3 in Hajek 2002 *}

(* Satallax succeeds, but Leo2 and Metis fail *)

  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists>e \<Phi>))]"
  (* sledgehammer [remote_satallax remote_leo2] (A12) *)
  (* by (metis A12) *)
  sorry
  
  corollary C1: "[\<diamond> (\<exists>e G)]"
  by (metis T1 A3)

  lemma L1: "[\<forall>e(\<lambda>u.( (G u) m\<rightarrow> (\<box> (G u) ) ) ) ]"
  by (metis (erased, lifting) A3 G_def)

subsection {* Independence of A4 *}
 
  lemma A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 
  nitpick [user_axioms, expect = genuine]
  nitpick [user_axioms, expect = genuine, satisfy]
  oops

subsection {* Provability of T3 *}

  axiomatization where A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 

  axiomatization where 
    trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)" and
    sym:   "x r y \<longrightarrow> y r x"

text {* Lemma L3 appears as Lemma 3.4 in Hajek 2002 and Aux1 appears in the proof of L3 *}

  lemma Aux1: "[\<forall>(\<lambda>\<Phi>. (P \<Phi>) m\<rightarrow> (\<forall>e(\<lambda>y.((G y) m\<rightarrow> (\<box>(\<Phi> y)) )) ) ) ]"
  by (metis G_def)

  lemma L3: "[\<forall>(\<lambda>\<Phi>. (P \<Phi>) m\<rightarrow> (\<box> (\<forall>e(\<lambda>y.((G y) m\<rightarrow> (\<Phi> y))) ) ) )]"
  (* sledgehammer min [remote_satallax] (Aux1 trans sym A4) *)
  by (metis Aux1 trans sym A4)

(* Satallax succeeds, but Metis fails *)
  
  theorem T3: "[\<box> (\<exists>e G)]"
  (* sledgehammer min [remote_satallax, verbose] (T1 L3 A3 A4 sym trans G_def) *)
  (* by (metis T1 L3 A3 A4 sym trans G_def) *)
  sorry

text {* Interesting fact: A5 was not needed to prove T3 above *}

(* ToDo: Hajek (2002) has a step by step derivation of T3, with a few auxiliary lemmas.
   Metis could succeed if given the auxiliary lemmas. *)


subsection {* Consistency again (now with sym and trans) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms] oops


subsection {* Independence of A5 *}

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>e(\<lambda>y. \<Phi> y)))))"

  lemma A5: "[P NE]"
  nitpick [satisfy, user_axioms, expect = genuine]
  nitpick [user_axioms, expect = genuine]
  oops


end
