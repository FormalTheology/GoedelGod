theory GoedelGodWithoutConjunctInEss_KB_var 
imports  Main "../QML_var"

begin
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  axiomatization where A1a: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. P (\<lambda>x. \<^bold>\<not> (\<Phi> x)) \<^bold>\<rightarrow> \<^bold>\<not> (P \<Phi>))\<rfloor>"
                   and A2:  "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. \<^bold>\<forall>(\<lambda>\<Psi>. (P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>E(\<lambda>x. \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" 

-- {* Positive properties are possibly exemplified. *}
  theorem T1: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>\<^sup>E \<Phi>))\<rfloor>"                                 by (metis A1a A2)

  definition ess (infixr "ess" 85) where "\<Phi> ess x = \<^bold>\<forall>(\<lambda>\<Psi>. \<Psi> x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>\<^sup>E(\<lambda>y. \<Phi> y \<^bold>\<rightarrow> \<Psi> y)))"

-- {* The empty property is an essence of every individual. *}
  lemma Lemma1: "\<lfloor>(\<^bold>\<forall>\<^sup>E(\<lambda>x.( (\<lambda>y.\<lambda>w. False) ess x)))\<rfloor>"                      by (metis ess_def)

  definition NE  where "NE x = \<^bold>\<forall>(\<lambda>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<exists> \<Phi>))"
  axiomatization where sym: "x r y \<longrightarrow> y r x" 

-- {* Exemplification of necessary existence is not possible. *}
  lemma Lemma2: "\<lfloor>\<^bold>\<not> (\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>E NE))\<rfloor>"                              by (metis sym Lemma1 NE_def)

  axiomatization where A5:  "\<lfloor>P NE\<rfloor>"

-- {* Now the inconsistency follows from A5, T1 and Lemma2 *}
  lemma False                                                       by (metis A5 T1 Lemma2) 
end   