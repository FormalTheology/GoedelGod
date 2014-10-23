
theory Hajek2002_Section5_Natural_var
imports Main "../QML_var"

begin

section {* Hajek's Small Emendations *}

text {* This is the theory called AOE'' in Definition 13 of Section 5 of Hajek (2002)  *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

text {* P' is Hajek' P#. The symbol "#" is not allowed by Isabelle. 
        In Hajek's definition, a possibilistic universal quantifier was used.
        However, careful reading gives strong reason to believe that this was just a typo
        and an actualistic quantifier was intended. *}

  definition P' :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
            "P' = (\<lambda>\<Phi>. \<exists>(\<lambda>\<Psi>.((P \<Psi>) m\<and> (\<box> (\<forall>e(\<lambda>x.((\<Psi> x) m\<rightarrow> (\<Phi> x) ) )))  ) ))     "

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ( (\<box> (\<Phi> x ))) m\<equiv> P' \<Phi> ))" 

  axiomatization where
    A12:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow>  (m\<not> (P (\<lambda>y.( m\<not> (\<Psi> y)) ) ) )   ))]" and
    A3:  "[P (\<lambda>x. (G x) ) ]" 




subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of T1, C1 and L1 *}
  
(* Satallax succeeds, but Leo2 and Metis fail. *)

  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists>e \<Phi>))]"
  (* sledgehammer [provers = remote_satallax remote_leo2, verbose] (A12) *)
  (* by (metis A12) *)
  sorry

  corollary C1: "[\<diamond> (\<exists>e G)]"
  (* sledgehammer [remote_satallax remote_leo2, verbose] (T1 A3) *)
  by (metis (no_types, lifting) A3 T1)

  lemma L1: "[\<forall>e(\<lambda>u.( (G u) m\<rightarrow> (\<box> (G u) ) ) ) ]"
  (* sledgehammer [remote_satallax, verbose, timeout = 60] (G_def A3 P'_def) *)
  (* sledgehammer [remote_leo2, verbose, timeout = 60] (G_def A3 P'_def) *)
  by (metis (erased, lifting) A3 G_def P'_def)


subsection {* Provability of T3 *}

  axiomatization where sym:   "x r y \<longrightarrow> y r x"

(* when given (T1 L3 A3 A4 sym trans G_def P'_def) as facts,
   Leo2 succeeds, but Satallax and Metis fail.
   Sledgehammer with Leo2 minimize the list of facts to (T1 A3 sym G_def P'_def). 
   With this minimized list of facts, 
   Metis succeeds but Satallax still fails.
   Interestingly, Leo2 (or Sledgehammer) seems to be adding the 
   extra fact "ext" to obtain its proofs. Nevertheless, 
   Metis succeeds when called without "ext". Maybe Metis assumes it implicitly.
   Satallax still fails even when "ext" is explicitly provided. 
   To find out why Satallax is failing, this should be compared to T3 in "Hajek2002_Section4_var.thy".
   There Satallax succeeds. *)
  
  theorem T3: "[\<box> (\<exists>e G)]"
  (* sledgehammer min [remote_satallax, verbose, timeout = 60] (T1 L3 A3 A4 sym trans G_def P'_def) *)
  (* sledgehammer min [remote_satallax, verbose, timeout = 60] (T1 L3 A3 A4 sym trans G_def P'_def ext) *)
  (* sledgehammer min [remote_leo2, verbose] (T1 L3 A3 A4 sym trans G_def P'_def) *)
  (* sledgehammer min [remote_leo2, verbose] (T1 A3 sym G_def P'_def) *)
  (* sledgehammer min [remote_satallax, verbose] (T1 A3 sym G_def P'_def) *)
  (* sledgehammer min [remote_satallax, verbose] (T1 A3 sym G_def P'_def ext) *)
  by (metis T1 A3 sym G_def P'_def)
   
text {* Interesting fact: as in "Hajek2002_Section4_var.thy",  A4 and A5 were still not needed to prove T3! *}
 

subsection {* Independence of A4 *}

text {* Hájek writes P instead of the first occurrence of P' in his definition of A4. 
        However, the the rest of his text makes it clear that this was a typo. *} 

  lemma A4 : "[\<forall>(\<lambda>\<Phi>.((P' \<Phi>) m\<rightarrow> (\<box> (P' \<Phi>) )))]"
  nitpick [user_axioms]
  nitpick [satisfy, user_axioms]
  oops

  axiomatization where A4 : "[\<forall>(\<lambda>\<Phi>.((P' \<Phi>) m\<rightarrow> (\<box> (P' \<Phi>) )))]"

  axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

text {* A4 seems necessary to prove the interesting lemma L3 *}

  lemma Aux1: "[\<forall>(\<lambda>\<Phi>. (P \<Phi>) m\<rightarrow> (\<forall>e(\<lambda>y.((G y) m\<rightarrow> (\<box>(\<Phi> y)) )) ) ) ]"
  by (metis G_def P'_def)

  lemma L3: "[\<forall>(\<lambda>\<Phi>. (P \<Phi>) m\<rightarrow> (\<box> (\<forall>e(\<lambda>y.((G y) m\<rightarrow> (\<Phi> y))) ) ) )]"
  (* sledgehammer min [remote_satallax] (Aux1 P'_def trans sym A4) *)
  by (metis Aux1 P'_def trans sym A4)


subsection {* Consistency again (now with A4, sym and trans) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Independence of A5 *}

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>e(\<lambda>y. \<Phi> y)))))"

text {* The Old A5 is still independent, as before. *}

  lemma OldA5: "[P NE]"
  nitpick [user_axioms]
  nitpick [user_axioms, satisfy]
  oops

text {* However, the status of the new A5 is inconclusive.
        Neither a proof nor a counter-model could be found so far. *}

  lemma A5: "[P' NE]"
  (* nitpick [user_axioms] *)
  (* nitpick [user_axioms, satisfy] *)
  (* sledgehammer [provers = metis remote_satallax remote_leo2, verbose] (A12 A3 A4 G_def P'_def ess_def NE_def sym trans) *)
  oops

  axiomatization where A5: "[P' NE]"


subsection {* Consistency again (with A5) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms] oops


subsection {* Analysis of Pages 13 and 14 *}

(* ToDo: Theorem 6 and Lemmas 6, 7, 8 and 9 in Hajek 2002 deserve to be investigated *)



end
