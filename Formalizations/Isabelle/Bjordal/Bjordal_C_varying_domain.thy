(*<*) 
theory Bjordal_C_varying_domain
imports Main QML_K_varying_domain

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
 where "P = (\<lambda>\<Phi>. \<box>(\<forall>e(\<lambda>x. G x m\<rightarrow> \<Phi> x)))" 

text {* We introduce Bjordal's definitions MCP and N. *}
 
 definition MCP :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  
 where "MCP = (\<lambda>\<Phi> x. \<Phi> x m\<and> P \<Phi> m\<and> 
   \<forall>(\<lambda>\<Psi>. (\<Psi> x m\<and> P \<Psi>) m\<rightarrow> \<box> (\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))"

 definition N :: "\<mu> \<Rightarrow> \<sigma>"  
 where "N = (\<lambda>x. \<forall>(\<lambda>\<Phi>. MCP \<Phi> x m\<rightarrow> \<box> (\<exists>e(\<lambda>y. \<Phi> y))))"  

text {* We postulate Bjordal's axioms Ax1 and Ax2. *}

 axiomatization where
  Ax1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))))]" and
  Ax2: "[P N]"

text {* We add axiom B (symmetry). *}

 axiomatization where sym: "x r y \<longrightarrow> y r x" 

text {* We prove possibly God exists and necessarily God exists. *}
 
 corollary C1: "[\<diamond> (\<exists>e G)]"  
 by (metis Ax1 P_def)

 theorem T3: "[\<box> (\<exists>e G)]" 
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis Ax1 Ax2 sym MCP_def N_def P_def) 

text {* Nitpick generates a countermodel to Modal Collapse. *}

 lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"  
 nitpick [user_axioms = true]
 oops

(*<*) 
end
(*>*) 