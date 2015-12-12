 theory ScottS5 imports Main QML_S5 
begin

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  axiomatization where
    A1a: "[(\<^bold>\<forall>\<Phi>. P(\<lambda>x. \<^bold>\<not>\<Phi>(x)) \<^bold>\<rightarrow> \<^bold>\<not>P(\<Phi>))]" and
    A1b: "[(\<^bold>\<forall>\<Phi>. \<^bold>\<not> P(\<Phi>) \<^bold>\<rightarrow> P(\<lambda>x. \<^bold>\<not>\<Phi>(x)))]" and
    A2:  "[(\<^bold>\<forall>\<Phi>. \<^bold>\<forall>\<Psi>. P(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> P(\<Psi>))]"
  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
         "G = (\<lambda>x. \<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"   
  axiomatization where 
    A3:  "[P(G)]" and 
    A4:  "[(\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<box>(P(\<Phi>)))]" 
  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
         "\<Phi> ess x = \<Phi>(x) \<^bold>\<and> (\<^bold>\<forall>\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y)))"
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
         "NE = (\<lambda>x. \<^bold>\<forall>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> \<Phi>))"
  axiomatization where 
    A5:  "[P NE]"

  theorem T3: "[\<^bold>\<box> (\<^bold>\<exists> G)]" -- {* LEO-II proves T3 directly from the axioms and definitions. *}
  sledgehammer [overlord,provers = remote_leo2 remote_satallax] (A1a A1b A2 A3 A4 A5 G_def NE_def ess_def )
  by (metis A1a A1b A2 A3 A4 A5 G_def NE_def ess_def)

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops  -- {* consistency *}

  lemma MC: "[\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)]"  -- {* Modal Collapse confirmed by LEO-II *}
  sledgehammer [provers = remote_leo2 remote_satallax] (T2 T3 ess_def)
  by (meson T2 T3 ess_def)
end
