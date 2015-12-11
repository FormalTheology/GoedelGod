theory GoedelGodWithoutConjunctInEss_K imports  Main QML
begin
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  definition ess (infixl "ess" 85) 
    where "\<Phi> ess x \<equiv> \<^bold>\<forall>\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y))"
  definition NE  where "NE x    \<equiv> \<^bold>\<forall>(\<lambda>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> \<Phi>))"
  axiomatization 
    where A1a: "[(\<^bold>\<forall>\<Phi>. P(\<lambda>x.\<^bold>\<not>(\<Phi>(x))) \<^bold>\<rightarrow> \<^bold>\<not>(P(\<Phi>)))]"
    and A2: "[(\<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>.(P(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x))) \<^bold>\<rightarrow> P(\<Psi>))]" 

-- {* Positive properties are possibly exemplified. *}
  theorem T1: "[(\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>(\<Phi>)))]"        by (metis A1a A2)

-- {* The empty property is an essence of every individual. *}
  lemma L1: "[(\<^bold>\<forall>x.((\<lambda>y.\<lambda>w. False) ess x))]"    by (metis ess_def)

  axiomatization where A5:  "[P NE]"

-- {* Now inconsistency follows from A5, L1, NE_def and T1 *}
  lemma False                          by (metis A5 L1 NE_def T1) 
end   
