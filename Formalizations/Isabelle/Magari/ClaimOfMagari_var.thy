(*<*) 
theory ClaimOfMagari_var
imports Main  "../QML_var"

begin
(*>*)


section {* G\"odel's Ontological Argument *}  

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<Phi> x))" 

  axiomatization where
    A1a: "[\<forall>(\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<rightarrow> m\<not> (P \<Phi>))]" and
    A1b: "[\<forall>(\<lambda>\<Phi>. m\<not> (P \<Phi>) m\<rightarrow> P (\<lambda>x. m\<not> (\<Phi> x)))]" and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" and
    A3:  "[P G]" 

  theorem T3: "[\<box> (\<exists> G)]" 
  nitpick [user_axioms]
  oops

(*<*) 
end
(*>*) 