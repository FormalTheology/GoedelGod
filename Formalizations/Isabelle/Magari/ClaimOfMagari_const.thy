(*<*) 
theory ClaimOfMagari_const
imports Main  "../QML"

begin
(*>*)


section {* G\"odel's Ontological Argument *}  

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G x \<equiv> \<^bold>\<forall>\<Phi>.(P \<Phi> \<^bold>\<rightarrow> \<Phi> x)" 

  axiomatization where
    A1a: "\<lfloor>\<^bold>\<forall>\<Phi>.( P (\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P \<Phi>))\<rfloor>" and
    A1b: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<not> (P \<Phi>) \<^bold>\<rightarrow> P (\<^sup>\<not>\<Phi>))\<rfloor>" and
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. ((P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>x.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" and
    A3:  "\<lfloor>P G\<rfloor>" 

  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>x. G x)\<rfloor>" 
  nitpick [user_axioms]
  oops

(*<*) 
end
(*>*) 