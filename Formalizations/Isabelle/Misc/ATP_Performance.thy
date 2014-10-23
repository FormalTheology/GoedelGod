
theory ATP_Performance
imports Main "../QML_var"

begin

section {* Interesting Problems for Understanding and Comparing ATP Performance *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G1 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G1 = (\<lambda>x. \<forall>(\<lambda>\<Phi>. (\<box> (\<Phi> x ))  m\<equiv>  ( \<exists>(\<lambda>\<Psi>.( (P \<Psi>) m\<and> (\<box> (\<forall>e(\<lambda>x. \<Psi> x m\<rightarrow> \<Phi> x))) )))  ))" 

  axiomatization where A3_1:  "[P G1]" 

  lemma L1_1: "[\<forall>e(\<lambda>u.( (G1 u) m\<rightarrow> (\<box> (G1 u) ) ) ) ]"
  sledgehammer [remote_satallax, verbose, timeout = 60] (G1_def A3_1)
  sledgehammer [remote_leo2, verbose, timeout = 60] (G1_def A3_1)
  by (metis (erased, lifting) A3_1 G1_def)

  definition P' :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
            "P' = (\<lambda>\<Phi>. \<exists>(\<lambda>\<Psi>.((P \<Psi>) m\<and> (\<box> (\<forall>e(\<lambda>x.((\<Psi> x) m\<rightarrow> (\<Phi> x) ) )))  ) ))     "

  definition G2 :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G2 = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ( (\<box> (\<Phi> x ))) m\<equiv> P' \<Phi> ))" 

  axiomatization where A3_2:  "[P (\<lambda>x. (G2 x) ) ]" 

  lemma L1_2: "[\<forall>e(\<lambda>u.( (G2 u) m\<rightarrow> (\<box> (G2 u) ) ) ) ]"
  sledgehammer [remote_satallax, verbose, timeout = 60] (G2_def A3_2 P'_def)
  sledgehammer [remote_leo2, verbose, timeout = 60] (G2_def A3_2 P'_def)
  by (metis (erased, lifting) A3_2 G2_def P'_def)


  axiomatization where A3_3:  "[P (\<lambda>x. (G1 x) ) ]" 

  lemma L1_3: "[\<forall>e(\<lambda>u.( (G1 u) m\<rightarrow> (\<box> (G1 u) ) ) ) ]"
  sledgehammer [remote_satallax, verbose, timeout = 60] (G1_def A3_3)
  sledgehammer [remote_leo2, verbose, timeout = 60] (G1_def A3_3)
  by (metis (erased, lifting) G1_def A3_3)

end
