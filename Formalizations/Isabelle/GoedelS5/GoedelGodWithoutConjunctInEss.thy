theory GoedelGodWithoutConjunctInEss 
imports  Main "../QML_S5"

begin
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  definition ess (infixr "ess" 85) where "\<Phi> ess x = \<^bold>\<forall>(\<lambda>\<Psi>. \<Psi> x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>(\<lambda>y. \<Phi> y \<^bold>\<rightarrow> \<Psi> y)))"
  definition NE  where                   "NE x    = \<^bold>\<forall>(\<lambda>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<exists> \<Phi>))"
  axiomatization where A1a: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. P (\<lambda>x. \<^bold>\<not> (\<Phi> x)) \<^bold>\<rightarrow> \<^bold>\<not> (P \<Phi>))\<rfloor>"
                   and A2:  "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. \<^bold>\<forall>(\<lambda>\<Psi>. (P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>(\<lambda>x. \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" 

-- {* Positive properties are possibly exemplified. *}
  theorem T1: "\<lfloor>\<^bold>\<forall>(\<lambda>\<Phi>. P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists> \<Phi>))\<rfloor>"                                
  by (metis A1a A2)

-- {* The empty property is an essence of every individual. *}
  lemma Lemma1: "\<lfloor>(\<^bold>\<forall>(\<lambda>x.((\<lambda>y.\<lambda>w. False) ess x)))\<rfloor>"                       
  by (metis ess_def)

  axiomatization where A5:  "\<lfloor>P NE\<rfloor>"

-- {* Now the inconsistency follows from A5, Lemma1, NE_def and T1 *}
  lemma False          
  sledgehammer [remote_leo2 remote_satallax] (A1a A2 A5 NE_def)
  sledgehammer [remote_leo2 remote_satallax] (A1a A2 A5 Lemma1 NE_def)
  by (metis A1a A2 A5 Lemma1 NE_def)
  -- {* by (metis A5 NE_def T1) *}


  by (metis A5 Lemma1 NE_def T1) 
end   
 