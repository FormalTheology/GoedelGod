theory God_D_Experiments
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
  lemma L11: "(G \<^bold>\<in> E)" (* this shows that the assumption of possibility is not needed. *)
  by (metis CONT4 IDEN2 NEG1 NG N_def POSS2 disjunction_def)

  (* this shows that necessity of concept implication reflects concept containment *)
  lemma L12: "\<forall>X.\<forall>Y.( (N (disjunction (not X) Y) ) \<longrightarrow> (contains X Y))" 
  by (metis CONT4 IDEN2 NEG1 N_def POSS2 disjunction_def)

  lemma L13: "\<forall>X.\<forall>Y.( (contains X Y)) \<longrightarrow>  (N (disjunction (not X) Y) )" 
  by (metis CONT4 IDEN2 NEG1 N_def POSS2 disjunction_def) 
 
 end

context (* Short proof attempt with axiom (N G) *)
 assumes 
  NG: "N G"
 begin
  lemma L10': "(P G) \<longrightarrow> (G \<^bold>\<in> E)" 
  nitpick [user_axioms, show_all, format = 2] sorry
 end


