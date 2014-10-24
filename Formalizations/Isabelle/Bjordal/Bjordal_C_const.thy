(*<*) 
theory Bjordal_C_const
imports Main "../QML"

begin
(*>*)

section {* Introduction *}

text {* We verify Frode Bjordal's paper from 1998. 
In this file Bjordal_C.thy we check the claim whether
his definitions for MCP and N together with his two axioms 
Ax1 and Ax2 imply necessary existence of God. *}

section {* Bjordal's argument *}  
 
text {* Constant symbol @{text "P"} (for 'Positive') is introduced
here as a primitive constant. Then G is defined using P. This is
Gödel's definition D1. *}  

text {* Constant symbol @{text "G"} (for 'God') is introduced
here as a primitive constant. Then P is defined using G. This
is Bjordal's definition D. *}

 consts G :: "\<mu> \<Rightarrow> \<sigma>"   
 definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
 where "P = (\<lambda>\<Phi>. \<box>(\<forall>(\<lambda>x. G x m\<rightarrow> \<Phi> x)))" 

text {* We introduce Bjordal's definitions MCP and N. *}
 
 definition MCP :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  
 where "MCP = (\<lambda>\<Phi> x. \<Phi> x m\<and> P \<Phi> m\<and> 
   \<forall>(\<lambda>\<Psi>. (\<Psi> x m\<and> P \<Psi>) m\<rightarrow> \<box> (\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))"

 definition N :: "\<mu> \<Rightarrow> \<sigma>"  
 where "N = (\<lambda>x. \<forall>(\<lambda>\<Phi>. MCP \<Phi> x m\<rightarrow> \<box> (\<exists>(\<lambda>y. \<Phi> y))))"  

text {* We postulate Bjordal's axioms Ax1 and Ax2. *}

 axiomatization where
  Ax1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))))]" and
  Ax2: "[P N]"

text {* We add axiom B (symmetry). *}

 axiomatization where sym: "x r y \<longrightarrow> y r x" 

text {* We prove necessarily God exists. *}
 
 theorem T3: "[\<box> (\<exists> G)]" 
 (* nitpick [user_axioms = true] *)
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis Ax1 Ax2 sym MCP_def N_def P_def) 

text {* Nitpick generates a countermodel to Modal Collapse. *}

 lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"  
 nitpick [user_axioms = true] oops


  abbreviation f_collapse_contingent_to_necessary :: "\<sigma> \<Rightarrow> \<sigma>" ("cCN")
         where "cCN \<Phi> \<equiv> \<Phi> m\<rightarrow> (\<box> \<Phi>)"

  abbreviation f_collapse_possible_to_necessary :: "\<sigma> \<Rightarrow> \<sigma>" ("cPN") 
         where "cPN \<Phi> \<equiv> (\<diamond> \<Phi>) m\<rightarrow> (\<box> \<Phi>)" 

  abbreviation f_collapse :: "\<sigma> \<Rightarrow> \<sigma>" ("c") 
         where "c \<Phi> \<equiv> (\<Phi> m\<equiv> (\<box> \<Phi>)) m\<and> ((\<box> \<Phi>) m\<equiv> (\<diamond> \<Phi>)) "

  abbreviation collapseCN  :: "\<sigma>" ("collapseCN") where "collapseCN \<equiv> \<forall>(\<lambda>\<Phi>. (cCN \<Phi>))"
  abbreviation collapsePN :: "\<sigma>" ("collapsePN") where "collapsePN \<equiv> \<forall>(\<lambda>\<Phi>. (cPN \<Phi>))"
  abbreviation collapse :: "\<sigma>" ("collapse") where "collapse \<equiv> \<forall>(\<lambda>\<Phi>. (c \<Phi>))"

  lemma "[collapseCN]"
  nitpick [user_axioms] oops
  
  lemma "[collapsePN]"
  nitpick [user_axioms] oops
  
  lemma "[collapse]"
  nitpick [user_axioms] oops
  
  lemma MC1: "[\<forall>(\<lambda>\<phi>.\<forall>(\<lambda>x.(((P \<phi>) m\<and> (G x) ) m\<rightarrow> ((\<phi> x) m\<rightarrow> (\<box> (\<phi> x))))))]"
  nitpick [user_axioms] oops
 
  lemma MC2: "[\<forall>(\<lambda>\<phi>.\<forall>(\<lambda>x.((G x) m\<rightarrow> ((\<phi> x) m\<rightarrow> (\<box> (\<phi> x))))))]"
  nitpick [user_axioms] oops

  lemma MC3: "[\<forall>(\<lambda>\<phi>.\<forall>(\<lambda>x.((P \<phi>) m\<rightarrow> ((\<phi> x) m\<rightarrow> (\<box> (\<phi> x))))))]"
  nitpick [user_axioms] oops


(*<*) 
end
(*>*) 