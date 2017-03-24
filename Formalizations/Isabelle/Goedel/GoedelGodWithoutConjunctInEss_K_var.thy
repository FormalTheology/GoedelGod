theory GoedelGodWithoutConjunctInEss_K_var 
imports Main "../QML_var"

begin
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  definition ess (infixr "ess" 85) where "\<Phi> ess x \<equiv> \<^bold>\<forall>\<Psi>.( \<Psi> x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ey.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y)))"
  definition NE  where                   "NE x \<equiv> \<^bold>\<forall>\<Phi>.( \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. \<Phi> x))"
  axiomatization where A1a: "\<lfloor>\<^bold>\<forall>\<Phi>.( P (\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P \<Phi>))\<rfloor>"
                   and A2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( (P \<Phi> \<^bold>\<and>  \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" 

-- {* Positive properties are possibly exemplified. *}
  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. \<Phi> x))\<rfloor>"                                 by (metis A1a A2)

-- {* The empty property is an essence of every individual. *}
  lemma Lemma1: "\<lfloor>(\<^bold>\<forall>\<^sup>Ex.(((\<lambda>y.\<lambda>w. False) ess x)))\<rfloor>"                       by (metis ess_def)

  axiomatization where A5:  "\<lfloor>P NE\<rfloor>"

-- {* Now the inconsistency follows from A5, Lemma1, NE_def and T1 *}
  lemma False          
  -- {* sledgehammer [remote_leo2] *}
                                                             by (metis A5 Lemma1 NE_def T1) 
end   
 