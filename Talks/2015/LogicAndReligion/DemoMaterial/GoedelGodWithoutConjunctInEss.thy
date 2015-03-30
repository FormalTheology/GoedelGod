theory GoedelGodWithoutConjunctInEss imports QML
begin
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  definition ess (infixr "ess" 85) where "\<Phi> ess x = \<forall>(\<lambda>\<Psi>. \<Psi> x m\<rightarrow> \<box> (\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y)))"
  definition NE  where                   "NE x    = \<forall>(\<lambda>\<Phi>. \<Phi> ess x m\<rightarrow> \<box> (\<exists> \<Phi>))"
  axiomatization where A1a: "[\<forall>(\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<rightarrow> m\<not> (P \<Phi>))]"
                   and A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" 
                   and A5:  "[P NE]"

-- {* Positive properties are possibly exemplified. *}
  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists> \<Phi>))]"                                     by (metis A1a A2)

-- {* Necessarily, the empty property is an essence of every individual. *}
  lemma Lemma1: "[\<box> (\<forall>(\<lambda>x.((\<lambda>y.\<lambda>w. False) ess x)))]"                         by (metis ess_def)

-- {* Exemplification of necessary existence is impossible. *}
  lemma Lemma2: "[m\<not> (\<diamond> (\<exists> NE))]"                            by (metis A5 A1a A2 Lemma1 NE_def)

-- {* Now the inconsistency easily follows A1a A2 A5 and Lemma2. *}
  lemma False                                                           by (metis T1 A5 Lemma2) 
end   
 