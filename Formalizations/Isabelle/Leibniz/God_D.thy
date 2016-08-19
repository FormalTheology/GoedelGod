theory God_D
imports AoC

begin
consts 
 E :: "c" ("E!")  
 G :: "c" ("G")

definition N :: "c \<Rightarrow> bool" where "N A \<equiv> \<not> P (\<^bold>~ A) "

context (* Short proof with axiom N((\<^bold>~G) \<^bold>\<or> E!) *)
 assumes 
  NG: "N((\<^bold>~G) \<^bold>\<or> E!)"
 begin
  lemma L10: "(P G) \<longrightarrow> (G \<^bold>\<in> E)" 
  by (metis CONJ3 NEG1 NEG2 NG N_def POSS1 POSS2 disjunction_def equal_def)
 end

context (* Short proof attempt with axiom (N G) *)
 assumes 
  NG: "N G"
 begin
  lemma L10': "(P G) \<longrightarrow> (G \<^bold>\<in> E)" 
  nitpick [user_axioms, show_all, format = 2] sorry
 end


