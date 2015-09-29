theory GoedelGodWithoutConjunctInEss_KB 
imports  Main "../QML"

begin
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  axiomatization where A1a: "[\<forall>(\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<rightarrow> m\<not> (P \<Phi>))]"
                   and A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" 

-- {* Positive properties are possibly exemplified. *}
  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists> \<Phi>))]"                                 by (metis A1a A2)

  definition ess (infixr "ess" 85) where "\<Phi> ess x = \<forall>(\<lambda>\<Psi>. \<Psi> x m\<rightarrow> \<box> (\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y)))"

-- {* The empty property is an essence of every individual. *}
  lemma Lemma1: "[(\<forall>(\<lambda>x.( (\<lambda>y.\<lambda>w. False) ess x)))]"                      by (metis ess_def)

  definition NE  where "NE x = \<forall>(\<lambda>\<Phi>. \<Phi> ess x m\<rightarrow> \<box> (\<exists> \<Phi>))"
  axiomatization where sym: "x r y \<longrightarrow> y r x" 

-- {* Exemplification of necessary existence is not possible. *}
  lemma Lemma2: "[m\<not> (\<diamond> (\<exists> NE))]"                              by (metis sym Lemma1 NE_def)

  axiomatization where A5:  "[P NE]"

-- {* Now the inconsistency follows from A5, T1 and Lemma2 *}
  lemma False                                                       by (metis A5 T1 Lemma2) 
end   