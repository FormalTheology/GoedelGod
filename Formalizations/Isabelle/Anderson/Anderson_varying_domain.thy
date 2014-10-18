(*<*) 
theory Anderson_varying_domain
imports Main QML_K_varying_domain

begin
(*>*)

section {* Anderson's Ontological Argument -- varying domain (individuals) *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<equiv>  ( (\<box> (\<Phi> x ))) ))" 

  axiomatization where
    A1:  "[\<forall>(\<lambda>\<Phi>. ((P \<Phi>) m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))) )  )]"  and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" and
    A3:  "[P G]" 

subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of T1, C and T3 *}
  
  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists>e \<Phi>))]"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2)
  
  corollary C1: "[\<diamond> (\<exists>e G)]"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3)

  text {* we only need axiom B here *}
  axiomatization where sym: "x r y \<longrightarrow> y r x"
    
  theorem T3: "[\<box> (\<exists>e G)]"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3 sym G_def)

subsection {* Consistency again (now with sym) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of A4 and A5 *}

  text {* As noted by Petr Hajek, A4 and A5 can be derived
          from the other axioms and definitions. *}
  
  text {* for A4 we need transitivity *}
  axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

  theorem A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A3 G_def sym trans T3)

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>e(\<lambda>y. \<Phi> y)))))"

  theorem A5: "[P NE]"
  by (metis A2 A3 ess_def NE_def)

  text{* Fuhrmann remarks that these derivations depend on 
       "meist stillschweigen gemachten Annahmen über die 
       Logik der zweiten Stufe, die Anderson jedoch nicht teilt." *}


subsection {* Consistency again (now with sym and trans) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms] oops



(*<*) 
end
(*>*) 
