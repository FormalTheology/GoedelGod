(*<*) 
theory ScottS5
imports Main "../QML_S5"

begin
(*>*)

section {* Introduction *}

section {* G\"odel's Ontological Argument *}  

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  axiomatization where
    A1a: "\<lfloor>\<^bold>\<forall>\<Phi>.( P (\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P \<Phi>))\<rfloor>" and
    A1b: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<not> (P \<Phi>) \<^bold>\<rightarrow> P (\<^sup>\<not>\<Phi>))\<rfloor>" and
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( (P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>x.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
 
  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>x. \<Phi> x))\<rfloor>"  
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A1a A2)

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<Phi> x)"   
 
  axiomatization where A3:  "\<lfloor>P G\<rfloor>" 

  corollary C: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>x. G x)\<rfloor>" 
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A3 T1)

  axiomatization where A4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>" 

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x \<equiv> \<Phi> x \<^bold>\<and>( \<^bold>\<forall>\<Psi>.( \<Psi> x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>y.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))"


  theorem T2: "\<lfloor>\<^bold>\<forall>x.( G x \<^bold>\<rightarrow> G ess x)\<rfloor>"
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A1b A4 G_def ess_def)

  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE x \<equiv> \<^bold>\<forall>\<Phi>.( \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<exists>x. \<Phi> x))"

  axiomatization where A5:  "\<lfloor>P NE\<rfloor>"


  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>x.  G x)\<rfloor>" 
  (*sledgehammer [provers = remote_leo2 remote_satallax] (A1a A1b A2 A3 A4 A5 G_def NE_def ess_def ) *)
  by (metis A1a A1b A2 A3 A4 A5 G_def NE_def ess_def)


text {* The consistency of the entire theory is confirmed by Nitpick. *}

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops

section {* Modal Collapse *}  

  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"  
(*  sledgehammer [provers = remote_leo2 remote_satallax] (T2 T3 ess_def) *)
  by (meson T2 T3 ess_def)

(*<*) 
end
(*>*) 