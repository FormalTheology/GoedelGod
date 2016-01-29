theory GoedelGodWithoutConjunctInEss_K imports QML
begin
 consts P :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"  
 definition ess (infixl "ess" 85) where 
  "\<Phi> ess x = (\<^bold>\<forall>\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y)))"
 definition NE  where                   
  "NE x = (\<^bold>\<forall>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> \<Phi>))"
 definition EmptyProperty ("\<^bold>\<emptyset>") where
  "\<^bold>\<emptyset> = (\<lambda>x.\<lambda>w. False)"

 axiomatization where 
  A1a: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>P(\<Phi>)\<rfloor>" and 
  A2: "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>. (P(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x))) \<^bold>\<rightarrow> P(\<Psi>)\<rfloor>" 

 theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>(\<Phi>))\<rfloor>"                                 
  by (metis A1a A2)

 lemma L1: "\<lfloor>\<^bold>\<forall>x.(\<^bold>\<emptyset> ess x)\<rfloor>"    (* Empty Essence Lemma *)                     
  by (metis EmptyProperty_def ess_def)

 axiomatization where 
  A5:  "\<lfloor>P NE\<rfloor>"

 lemma False                        (* Inconsistency *)         
  sledgehammer [remote_leo2]
by (metis A1a A2 A5 EmptyProperty_def NE_def T1)
  by (metis EmptyProperty_def A5 L1 NE_def T1) 
end   
