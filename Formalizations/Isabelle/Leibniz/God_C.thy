theory God_C
imports AoC

begin
consts 
 E :: "c" ("E!")  
 G :: "c" ("G")

definition N :: "c \<Rightarrow> bool" where "N A \<equiv> \<not> P (\<^bold>~ A) "

context (* Failing proof attempt with axiom (N G) *)
 assumes 
  NG: "N G"
 begin
  lemma L2: "\<not>(X \<^bold>\<in> E!) \<longrightarrow> (P (X \<^bold>+ \<^bold>~E!))"
    by (simp add: POSS2)
  lemma L3: "(P (X \<^bold>+ \<^bold>~E!)) \<longrightarrow> \<not>\<not>(P (X \<^bold>+ \<^bold>~E!)) "
    by simp
  lemma L4: "\<not>\<not>(P (X \<^bold>+ \<^bold>~E!)) \<longrightarrow> \<not>(N ((\<^bold>~X) \<^bold>\<or> E!))"
    by (smt CONJ1 CONJ4 CONJ5 CONT2 IDEN2 NEG1 N_def POSS1 disjunction_def equal_def) 
  lemma L5: "\<not>(G \<^bold>\<in> E) \<longrightarrow> \<not>(N ((\<^bold>~G) \<^bold>\<or> E!))"
    by (simp add: L4 L2)
  lemma L6: "\<not>(N ((\<^bold>~G) \<^bold>\<or> E!)) \<or>  \<not>\<not>(N ((\<^bold>~G) \<^bold>\<or> E!))" 
    by simp
  lemma L7: "\<not>(N ((\<^bold>~G) \<^bold>\<or> E!)) \<longrightarrow> \<not>(P G)" 
    nitpick [user_axioms, show_all, format = 2] sorry
end


    (*
   Nitpick found a counterexample for card c = 2:
   Constants:
    op \<^bold>+ = (\<lambda>x. _)((c\<^sub>1, c\<^sub>1) := c\<^sub>1, (c\<^sub>1, c\<^sub>2) := c\<^sub>1, (c\<^sub>2, c\<^sub>1) := c\<^sub>1, (c\<^sub>2, c\<^sub>2) := c\<^sub>2)
    op \<^bold>\<in> = (\<lambda>x. _)((c\<^sub>1, c\<^sub>1) := True, (c\<^sub>1, c\<^sub>2) := True, (c\<^sub>2, c\<^sub>1) := False, (c\<^sub>2, c\<^sub>2) := True)
    not = (\<lambda>x. _)(c\<^sub>1 := c\<^sub>2, c\<^sub>2 := c\<^sub>1)
    E! = c\<^sub>1
    G = c\<^sub>2 
    *)


context (* Proof with axiom N((\<^bold>~G) \<^bold>\<or> E!) *)
 assumes 
  NG: "N((\<^bold>~G) \<^bold>\<or> E!)"
 begin
  lemma L2': "\<not>(X \<^bold>\<in> E!) \<longrightarrow> (P (X \<^bold>+ \<^bold>~E!))"
    by (simp add: POSS2)
  lemma L3': "(P (X \<^bold>+ \<^bold>~E!)) \<longrightarrow> \<not>\<not>(P (X \<^bold>+ \<^bold>~E!)) "
    by simp
  lemma L4': "\<not>\<not>(P (X \<^bold>+ \<^bold>~E!)) \<longrightarrow> \<not>(N ((\<^bold>~X) \<^bold>\<or> E!))"
    by (smt CONJ1 CONJ4 CONJ5 CONT2 IDEN2 NEG1 N_def POSS1 disjunction_def equal_def) 
  lemma L5': "\<not>(G \<^bold>\<in> E) \<longrightarrow> \<not>(N ((\<^bold>~G) \<^bold>\<or> E!))"
    by (simp add: L4' L2')
  lemma L6': "\<not>(N ((\<^bold>~G) \<^bold>\<or> E!)) \<or> \<not>\<not>(N ((\<^bold>~G) \<^bold>\<or> E!))" 
    by simp
  lemma L7': "\<not>(N ((\<^bold>~G) \<^bold>\<or> E!)) \<longrightarrow> \<not>(P G)" 
    by (simp add: NG)
  lemma L8': "\<not>\<not>(N ((\<^bold>~G) \<^bold>\<or> E!)) \<longrightarrow> \<not>\<not>(G \<^bold>\<in> E)" 
    using L5' by blast
  lemma L9': "\<not>(P G) \<or> (G \<^bold>\<in> E)" 
    using L6' L7' L8' by metis
  lemma L10': "(P G) \<longrightarrow> (G \<^bold>\<in> E)" 
  using L9' by auto
end
