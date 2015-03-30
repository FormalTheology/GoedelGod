theory GoedelGodWithoutConjunctInEss_var imports QML_var
begin
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  definition ess (infixr "ess" 85) where "\<Phi> ess x = \<forall>(\<lambda>\<Psi>. \<Psi> x m\<rightarrow> \<box> (\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y)))"
  definition NE  where                   "NE x    = \<forall>(\<lambda>\<Phi>. \<Phi> ess x m\<rightarrow> \<box> (\<exists>e \<Phi>))"
  axiomatization where A1a: "[\<forall>(\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<rightarrow> m\<not> (P \<Phi>))]"
                   and A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" 
                   and A5:  "[P NE]"

-- {* The empty property is an essence of any individual. *}
  lemma Lemma1: "[\<forall>e(\<lambda>x.((\<lambda>y.\<lambda>w. False) ess x))]"                             by (metis ess_def)

-- {* NE is not exemplified. *}
  lemma Lemma2: "[m\<not> (\<exists>e NE)]"                                by (metis A5 A1a A2 Lemma1 NE_def)

-- {* Positive properties are possibly exemplified. *}
  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists>e \<Phi>))]"                                     by (metis A1a A2)

-- {* Now the inconsistency easily follows A1a A2 A5 and Lemma2. *}
  lemma False                                                            by (metis T1 A5 Lemma2) 

-- {* A5 could be weakened: P is exemplified.*}
  lemma Lemma3: "[(\<exists> P) m\<rightarrow> (m\<not> (\<exists>e NE))]"                       by (metis A1a A2 Lemma1 NE_def)
end   
 