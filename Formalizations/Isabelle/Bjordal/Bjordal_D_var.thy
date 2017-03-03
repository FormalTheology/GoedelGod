
theory Bjordal_D_var
imports Main "../QML_S5_var"

begin

section {* Non-Superfluousness of A5 *}

text {* Here we investigate whether the remarks in the last paragraph of Bjordal (1998).
        We check whether A5 is superfluous for deriving the necessary existence of God 
        and we conclude that it is not. *}

 consts G :: "\<mu> \<Rightarrow> \<sigma>"   
 definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
 where "P = (\<lambda>\<Phi>. \<^bold>\<box>(\<^bold>\<forall>\<^sup>E(\<lambda>x. G x \<^bold>\<rightarrow> \<Phi> x)))" 
 
 definition MCP :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  
 where "MCP = (\<lambda>\<Phi> x. \<Phi> x \<^bold>\<and> P \<Phi> \<^bold>\<and> 
   \<^bold>\<forall>(\<lambda>\<Psi>. (\<Psi> x \<^bold>\<and> P \<Psi>) \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>\<^sup>E(\<lambda>y. \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))"

 definition N :: "\<mu> \<Rightarrow> \<sigma>"  
 where "N = (\<lambda>x. \<^bold>\<forall>(\<lambda>\<Phi>. MCP \<Phi> x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<exists>\<^sup>E(\<lambda>y. \<Phi> y))))"  

 axiomatization where A1: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<^bold>\<not> (P (\<lambda>x. \<^bold>\<not> (\<Phi> x))))\<rfloor>"

 corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>E G)\<rfloor>"  
 by (metis A1 P_def)

text {* To make our upcoming negative result stronger, we add use S5U *}


text {* Without A5, T3 is independent. Nitpick finds both a model and a counter-model.
        Therefore, A5 is not superfluous.        
*}

 theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>E G)\<rfloor>"
 nitpick [user_axioms]
 nitpick [user_axioms, satisfy]
 oops

end
