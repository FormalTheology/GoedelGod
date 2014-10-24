
theory Bjordal_D_var
imports Main "../QML_var"

begin

section {* Non-Superfluousness of A5 *}

text {* Here we investigate whether the remarks in the last paragraph of Bjordal (1998).
        We check whether A5 is superfluous for deriving the necessary existence of God 
        and we conclude that it is not. *}

 consts G :: "\<mu> \<Rightarrow> \<sigma>"   
 definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
 where "P = (\<lambda>\<Phi>. \<box>(\<forall>e(\<lambda>x. G x m\<rightarrow> \<Phi> x)))" 
 
 definition MCP :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  
 where "MCP = (\<lambda>\<Phi> x. \<Phi> x m\<and> P \<Phi> m\<and> 
   \<forall>(\<lambda>\<Psi>. (\<Psi> x m\<and> P \<Psi>) m\<rightarrow> \<box> (\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))"

 definition N :: "\<mu> \<Rightarrow> \<sigma>"  
 where "N = (\<lambda>x. \<forall>(\<lambda>\<Phi>. MCP \<Phi> x m\<rightarrow> \<box> (\<exists>e(\<lambda>y. \<Phi> y))))"  

 axiomatization where A1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))))]"

 corollary C1: "[\<diamond> (\<exists>e G)]"  
 by (metis A1 P_def)

text {* To make our upcoming negative result stronger, we add all the following axioms. *}

 axiomatization where  sym:   "x r y \<longrightarrow> y r x" 
                  and  trans: "x r y \<and> y r z \<longrightarrow> x r y"
                  and  refl:  "x r x"


text {* Without A5, T3 is independent. Nitpick finds both a model and a counter-model.
        Therefore, A5 is not superfluous.        
*}

 theorem T3: "[\<box> (\<exists>e G)]"
 nitpick [user_axioms]
 nitpick [user_axioms, satisfy]
 oops

end
