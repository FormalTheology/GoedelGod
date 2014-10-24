(*<*) 
theory Bjordal_D_var
imports Main "../QML_var"

begin
(*>*)

section {* Introduction *}

text {* We verify Frode Bjordal's paper from 1998. 
In this file Bjordal_D.thy we check the remarks in his last paragraph.
We check whether Ax2 is superfluous for deriving the necessary existence of God. *}

(* ToDo *)
(* Everything below is still a copy-paste of Bjordal_C *)

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