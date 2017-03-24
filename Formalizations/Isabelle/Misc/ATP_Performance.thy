
theory ATP_Performance
imports Main "../QML_var"

begin

section {* Interesting Problems for Understanding and Comparing ATP Performance *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G1 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1 x \<equiv> \<^bold>\<forall>\<Phi>.( (\<^bold>\<box> (\<Phi> x ))  \<^bold>\<leftrightarrow>  ( \<^bold>\<exists>\<Psi>.(( (P \<Psi>) \<^bold>\<and> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Psi> x \<^bold>\<rightarrow> \<Phi> x))) )) ))" 

  axiomatization where A3_1:  "\<lfloor>P G1\<rfloor>" 

  lemma L1_1: "\<lfloor>\<^bold>\<forall>\<^sup>Eu.(( (G1 u) \<^bold>\<rightarrow> (\<^bold>\<box> (G1 u) ) ) ) \<rfloor>"
(*  sledgehammer [remote_satallax, verbose, timeout = 60] (G1_def A3_1)
  sledgehammer [remote_leo2, verbose, timeout = 60] (G1_def A3_1)*)
  by (metis (erased, lifting) A3_1 G1_def)

  definition P' :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
            "P' \<Phi> \<equiv> \<^bold>\<exists>\<Psi>.(((P \<Psi>) \<^bold>\<and> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.(((\<Psi> x) \<^bold>\<rightarrow> (\<Phi> x) ) )))))"

  definition G2 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G2 x \<equiv> \<^bold>\<forall>\<Phi>.( ( (\<^bold>\<box> (\<Phi> x ))) \<^bold>\<leftrightarrow> P' \<Phi> )" 

  axiomatization where A3_2:  "\<lfloor>P G2\<rfloor>" 

  lemma L1_2: "\<lfloor>\<^bold>\<forall>\<^sup>Eu.((G2 u) \<^bold>\<rightarrow> (\<^bold>\<box> (G2 u) ) )\<rfloor>"
(*  sledgehammer [remote_satallax, verbose, timeout = 60] (G2_def A3_2 P'_def)
  sledgehammer [remote_leo2, verbose, timeout = 60] (G2_def A3_2 P'_def)*)
  by (metis (erased, lifting) A3_2 G2_def P'_def)


  axiomatization where A3_3:  "\<lfloor>P G1\<rfloor>" 

  lemma L1_3: "\<lfloor>\<^bold>\<forall>\<^sup>Eu.(( (G1 u) \<^bold>\<rightarrow> (\<^bold>\<box> (G1 u) ) ) ) \<rfloor>"
(*  sledgehammer [remote_satallax, verbose, timeout = 60] (G1_def A3_3)
  sledgehammer [remote_leo2, verbose, timeout = 60] (G1_def A3_3)*)
  by (metis (erased, lifting) G1_def A3_3)

end
