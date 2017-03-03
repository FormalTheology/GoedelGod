(*<*) 
theory ClaimOfMagari_var
imports Main  "../QML_var"

begin
(*>*)


section {* G\"odel's Ontological Argument *}  

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<^bold>\<forall>(\<lambda>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<Phi> x))" 

  axiomatization where
    A1a: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. P (\<lambda>x. \<^bold>\<not> (\<Phi> x)) \<^bold>\<rightarrow> \<^bold>\<not> (P \<Phi>))\<rfloor>" and
    A1b: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. \<^bold>\<not> (P \<Phi>) \<^bold>\<rightarrow> P (\<lambda>x. \<^bold>\<not> (\<Phi> x)))\<rfloor>" and
    A2:  "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. \<^bold>\<forall>(\<lambda>\<Psi>. (P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>E(\<lambda>x. \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" and
    A3:  "\<lfloor>P  G\<rfloor>" 

  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists> G)\<rfloor>" 
  nitpick [user_axioms]
  oops

(*<*) 
end
(*>*) 