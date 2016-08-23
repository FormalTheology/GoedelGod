theory God_fail
imports AoC_Implication

begin
consts
  E :: "c" ("E") (*Concept of existence*)
  G :: "c" ("G") (*Concept god/being godlike*)
axiomatization where 
GnotE:"G \<^bold>\<noteq> E" and
GnotnotE: "G \<^bold>\<noteq> \<^bold>~E"

(*Proof attempt fails, if necessity is understood as "N G"*)
definition N :: "c \<Rightarrow> bool" where "N A \<equiv> \<not> P (\<^bold>~ A) "

axiomatization where
  NG: "N G"

lemma L7: "\<not>(N (G \<^bold>\<longrightarrow> E)) \<longrightarrow> \<not>(P G)" 
  nitpick [user_axioms, show_all, format = 2] oops




lemma L2: "\<not>(X \<^bold>\<sqsupset> E) \<longrightarrow> (P (X \<^bold>+ \<^bold>~E))"
 by (simp add: POSS2)
lemma L3: "(P (X \<^bold>+ \<^bold>~E)) \<longrightarrow> \<not>\<not>(P (X \<^bold>+ \<^bold>~E)) "
  by simp
lemma L4: "\<not>\<not>(P (X \<^bold>+ \<^bold>~E)) \<longrightarrow> \<not>(N (G \<^bold>\<longrightarrow> E))"
 using CONJ1 CONJ4 CONJ5 CONT2 IDEN2 NEG1 N_def POSS1 disjunction_def
 equal_def implication_def POSS2 NG by metis
lemma L5: "\<not>(G \<^bold>\<sqsupset> E) \<longrightarrow> \<not>(N (G \<^bold>\<longrightarrow> E))"
  using L2 L4 by auto
lemma L6: "\<not>(N (G \<^bold>\<longrightarrow> E)) \<or>  \<not>\<not>(N (G \<^bold>\<longrightarrow> E))" 
  by simp
lemma L7: "\<not>(N (G \<^bold>\<longrightarrow> E)) \<longrightarrow> \<not>(P G)" 
    nitpick [user_axioms, show_all, format = 2] oops
(* Nitpick found a counterexample for card c = 2:
  Constants:
    op \<^bold>+ = (\<lambda>x. _)((c\<^sub>1, c\<^sub>1) := c\<^sub>1, (c\<^sub>1, c\<^sub>2) := c\<^sub>1, (c\<^sub>2, c\<^sub>1) := c\<^sub>1, (c\<^sub>2, c\<^sub>2) := c\<^sub>2)
    op \<^bold>\<sqsupset> = (\<lambda>x. _)((c\<^sub>1, c\<^sub>1) := True, (c\<^sub>1, c\<^sub>2) := True, (c\<^sub>2, c\<^sub>1) := False, (c\<^sub>2, c\<^sub>2) := True)
    not = (\<lambda>x. _)(c\<^sub>1 := c\<^sub>2, c\<^sub>2 := c\<^sub>1)    E = c\<^sub>1
    G = c\<^sub>2 *)

end
