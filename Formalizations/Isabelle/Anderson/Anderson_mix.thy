theory Anderson_mix
imports Main "../QML_var"

begin


section {* Anderson's Ontological Argument (with Mixed Quantifiers) *}

text {* Here we explore Anderson's remark, in footnote 14 of his 1990 article,
        that we ought to "take the existential quantifier in the definition of 
        necessary existence to be an [actualistic] e-quantifier [...] and so too 
        the quantifier in the conclusion of the argument. All other individual 
        quantifiers may be taken to be [possibilistic] subsistential, [...]".   *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<equiv>  ( (\<box> (\<Phi> x ))) ))" 

  axiomatization where
    A1:  "[\<forall>(\<lambda>\<Phi>. ((P \<Phi>) m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))) )  )]"  and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" and
    A3:  "[P G]" 


subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Provability of C1 *}
  
  corollary C1: "[\<diamond> (\<exists> G)]"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3)


subsection {* Provability of A4 *}

text {* As claimed by Hájek (1996) and contrary to footnote 1 in Anderson-Gettings (1996),
        A4 is redundant. *}

  axiomatization where 
    sym: "x r y \<longrightarrow> y r x" and
    trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"
    
  lemma AuxLemma1: "[\<box> (\<exists> G)]"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3 sym G_def)

  theorem A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A3 G_def sym trans AuxLemma1)


subsection {* Consistency (now with sym and trans) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Independence of A5 *}

text {* As claimed by Anderson-Gettings (1996) in footnote 1 and contrary to  Hájek's claim,
        A5 is not redundant. Nitpick finds a counter-model. *}

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>e(\<lambda>y. \<Phi> y)))))"

  theorem A5: "[P NE]"
  nitpick [user_axioms] 
  nitpick [user_axioms, satisfy] oops


subsection {* Immunity to Modal Collapse *}  
 
text {* As claimed by Anderson, the modal collapse is not provable. 
        Nitpick finds a counter-model. *}

  theorem MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms, expect = genuine]
  oops


subsection {* Counter-Satisfiability of the Main Theorem *}

text {* Unfortunately, with actualistic quantifiers only for NE and T3, 
        T3 is not provable. Nitpick finds a counter-model. *}

  theorem T3: "[\<box> (\<exists>e G)]"
  nitpick [user_axioms] oops

end
