
theory Bjordal_D_const
imports Main "../QML_S5"

begin


section {* Non-Superfluousness of A5 *}

text {* Here we investigate whether the remarks in the last paragraph of Bjordal (1998).
        We check whether A5 is superfluous for deriving the necessary existence of God 
        and we conclude that it is not. *}


 consts G :: "\<mu> \<Rightarrow> \<sigma>"   
 definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
 where "P \<Phi> \<equiv> \<^bold>\<box>(\<^bold>\<forall>x.( G x \<^bold>\<rightarrow> \<Phi> x))" 
 
 definition MCP :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>"  
 where "MCP \<Phi> x \<equiv> \<Phi> x \<^bold>\<and> P \<Phi> \<^bold>\<and> 
  ( \<^bold>\<forall>\<Psi>. ((\<Psi> x \<^bold>\<and> P \<Psi>) \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>y.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))"

 definition N :: "\<mu> \<Rightarrow> \<sigma>"  
 where "N x \<equiv> ( \<^bold>\<forall>\<Phi>.( MCP \<Phi> x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<exists>y.( \<Phi> y))))"  

 axiomatization where A1: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<not> (P ( \<^sup>\<not>\<Phi>)))\<rfloor>"

text {* To make our upcoming negative result stronger, we use S5U *}


text {* Without A5, T3 is independent. Nitpick finds both a model and a counter-model.
        Therefore, A5 is not superfluous.        
*}

 theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>x. G x)\<rfloor>"
 nitpick [user_axioms]
 nitpick [user_axioms, satisfy]
 oops


end
