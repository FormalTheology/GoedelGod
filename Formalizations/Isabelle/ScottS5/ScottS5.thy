(*<*) 
theory ScottS5
imports Main "../QML_S5"

begin
(*>*)

section {* Introduction *}

section {* G\"odel's Ontological Argument *}  

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  axiomatization where
    A1a: "[\<forall>(\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<rightarrow> m\<not> (P \<Phi>))]" and
    A1b: "[\<forall>(\<lambda>\<Phi>. m\<not> (P \<Phi>) m\<rightarrow> P (\<lambda>x. m\<not> (\<Phi> x)))]" and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]"
 
  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists> \<Phi>))]"  
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A1a A2)

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<Phi> x))"   
 
  axiomatization where A3:  "[P G]" 

  corollary C: "[\<diamond> (\<exists> G)]" 
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A3 T1)

  axiomatization where A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x m\<and> \<forall>(\<lambda>\<Psi>. \<Psi> x m\<rightarrow> \<box> (\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y)))"


  theorem T2: "[\<forall>(\<lambda>x. G x m\<rightarrow> G ess x)]"
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A1b A4 G_def ess_def)

  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. \<Phi> ess x m\<rightarrow> \<box> (\<exists> \<Phi>)))"

  axiomatization where A5:  "[P NE]"


  theorem T3: "[\<box> (\<exists> G)]" 
  sledgehammer [provers = remote_leo2 remote_satallax] (A1a A1b A2 A3 A4 A5 G_def NE_def ess_def )
  by (metis A1a A1b A2 A3 A4 A5 G_def NE_def ess_def)


text {* The consistency of the entire theory is confirmed by Nitpick. *}

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops

section {* Modal Collapse *}  

  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"  
  sledgehammer [provers = remote_leo2 remote_satallax] (T2 T3 ess_def)
  by (meson T2 T3 ess_def)

(*<*) 
end
(*>*) 