(*<*) 
theory Bjordal_C_var
imports Main "../QML_var"

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
 where "P = (\<lambda>\<Phi>. \<^bold>\<box>(\<^bold>\<forall>\<^sup>E(\<lambda>x. G x \<^bold>\<rightarrow> \<Phi> x)))" 

text {* We introduce Bjordal's definitions MCP and N. *}
 
 definition MCP :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  
 where "MCP = (\<lambda>\<Phi> x. \<Phi> x \<^bold>\<and> P \<Phi> \<^bold>\<and> 
   \<^bold>\<forall>(\<lambda>\<Psi>. (\<Psi> x \<^bold>\<and> P \<Psi>) \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>\<^sup>E(\<lambda>y. \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))"

 definition N :: "\<mu> \<Rightarrow> \<sigma>"  
 where "N = (\<lambda>x. \<^bold>\<forall>(\<lambda>\<Phi>. MCP \<Phi> x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<exists>\<^sup>E(\<lambda>y. \<Phi> y))))"  

text {* We postulate Bjordal's axioms Ax1 and Ax2. *}

 axiomatization where
  A1: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<^bold>\<not> (P (\<lambda>x. \<^bold>\<not> (\<Phi> x))))\<rfloor>" and
  A5: "\<lfloor>P N\<rfloor>"

text {* We add axiom B (symmetry). *}

 axiomatization where sym: "x r y \<longrightarrow> y r x" 

text {* We prove possibly God exists and necessarily God exists. *}
 
 corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>E G)\<rfloor>"  
 by (metis A1 P_def)

 theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>E G)\<rfloor>" 
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis A1 A5 sym MCP_def N_def P_def) 

text {* Nitpick generates a countermodel to Modal Collapse. *}

 lemma MC: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)))\<rfloor>"  
 nitpick [user_axioms = true] oops


  abbreviation f_collapse_contingent_to_necessary :: "\<sigma> \<Rightarrow> \<sigma>" ("cCN")
         where "cCN \<Phi> \<equiv> \<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)"

  abbreviation f_collapse_possible_to_necessary :: "\<sigma> \<Rightarrow> \<sigma>" ("cPN") 
         where "cPN \<Phi> \<equiv> (\<^bold>\<diamond> \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)" 

  abbreviation f_collapse :: "\<sigma> \<Rightarrow> \<sigma>" ("c") 
         where "c \<Phi> \<equiv> (\<Phi> \<^bold>\<leftrightarrow> (\<^bold>\<box> \<Phi>)) \<^bold>\<and> ((\<^bold>\<box> \<Phi>) \<^bold>\<leftrightarrow> (\<^bold>\<diamond> \<Phi>)) "

  abbreviation collapseCN  :: "\<sigma>" ("collapseCN") where "collapseCN \<equiv> \<^bold>\<forall>(\<lambda>\<Phi>. (cCN \<Phi>))"
  abbreviation collapsePN :: "\<sigma>" ("collapsePN") where "collapsePN \<equiv> \<^bold>\<forall>(\<lambda>\<Phi>. (cPN \<Phi>))"
  abbreviation collapse :: "\<sigma>" ("collapse") where "collapse \<equiv> \<^bold>\<forall>(\<lambda>\<Phi>. (c \<Phi>))"

  lemma "\<lfloor>collapseCN\<rfloor>"
  nitpick [user_axioms] oops
  
  lemma "\<lfloor>collapsePN\<rfloor>"
  nitpick [user_axioms] oops
  
  lemma "\<lfloor>collapse\<rfloor>"
  nitpick [user_axioms] oops
  
  lemma MC1: "\<lfloor>\<^bold>\<forall>(\<lambda>\<phi>.\<^bold>\<forall>(\<lambda>x.(((P \<phi>) \<^bold>\<and> (G x) ) \<^bold>\<rightarrow> ((\<phi> x) \<^bold>\<rightarrow> (\<^bold>\<box> (\<phi> x))))))\<rfloor>"
  nitpick [user_axioms] oops
 
  lemma MC2: "\<lfloor>\<^bold>\<forall>(\<lambda>\<phi>.\<^bold>\<forall>(\<lambda>x.((G x) \<^bold>\<rightarrow> ((\<phi> x) \<^bold>\<rightarrow> (\<^bold>\<box> (\<phi> x))))))\<rfloor>"
  nitpick [user_axioms] oops

  lemma MC3: "\<lfloor>\<^bold>\<forall>(\<lambda>\<phi>.\<^bold>\<forall>(\<lambda>x.((P \<phi>) \<^bold>\<rightarrow> ((\<phi> x) \<^bold>\<rightarrow> (\<^bold>\<box> (\<phi> x))))))\<rfloor>"
  nitpick [user_axioms] oops

(*<*) 
end
(*>*) 