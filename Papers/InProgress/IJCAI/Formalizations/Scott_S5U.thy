theory Scott_S5U imports QML_S5U 
begin
 consts P :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"  
 axiomatization where
  A1a: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>P(\<Phi>)\<rfloor>" and 
  A1b: "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<not>P(\<Phi>) \<^bold>\<rightarrow> P(\<^sup>\<not>\<Phi>)\<rfloor>" and 
  A2:  "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>. P(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> P(\<Psi>)\<rfloor>"
 definition G where 
  "G(x) = (\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"   
 axiomatization where 
  A3: "\<lfloor>P(G)\<rfloor>" and 
  A4: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<box>(P(\<Phi>))\<rfloor>" 
 definition ess (infixr "ess" 85) where
  "\<Phi> ess x = \<Phi>(x) \<^bold>\<and> (\<^bold>\<forall>\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y)))"
 definition NE where 
  "NE(x) = (\<^bold>\<forall>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> \<Phi>))"
 axiomatization where 
  A5:  "\<lfloor>P(NE)\<rfloor>"

 theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists> G)\<rfloor>" -- {* LEO-II proves T3 in 2,5sec *}
  sledgehammer [provers = remote_leo2]
  by (metis (lifting, full_types) 
     A1a A1b A2 A3 A4 A5 G_def NE_def ess_def)

 lemma True nitpick [satisfy,user_axioms,expect=genuine] oops  
 -- {* Consistency is confirmed by Nitpick *}

 theorem T2: "\<lfloor>\<^bold>\<forall>x. G(x) \<^bold>\<rightarrow> G ess x\<rfloor>"
  sledgehammer [provers = remote_leo2]
  by (metis A1b A4 G_def ess_def)

 lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)\<rfloor>"  -- {* Modal Collapse *}
  sledgehammer [provers = remote_satallax, timeout=600]
  by (meson T2 T3 ess_def)
end

