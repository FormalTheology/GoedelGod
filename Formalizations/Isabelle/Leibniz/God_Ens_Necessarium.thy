theory God_Ens_Necessarium
imports AoC

begin
consts
  E :: "c"
  G :: "c" ("G")

context (* Failing proof attempt with axiom (N G) *)
 assumes 
  NG: "N G" and
  GnotE:"G \<^bold>\<noteq> E" and
  GnotnotE: "G \<^bold>\<noteq> \<^bold>~E"
 begin
  lemma L2: "\<not>(X \<^bold>\<sqsupset> E) \<longrightarrow> (P (X \<^bold>+ \<^bold>~E))"
    by (simp add: POSS2)
  lemma L3: "(P (X \<^bold>+ \<^bold>~E)) \<longrightarrow> \<not>\<not>(P (X \<^bold>+ \<^bold>~E)) "
    by simp
  lemma L4: "\<not>\<not>(P (X \<^bold>+ \<^bold>~E)) \<longrightarrow> \<not>(N (G \<^bold>\<longrightarrow> E))"
    using CONJ1 CONJ4 CONJ5 CONT2 IDEN2 NEG1 necessary_def POSS1 disjunction_def equal_def implication_def POSS2 NG
    by metis
  lemma L5: "\<not>(G \<^bold>\<sqsupset> E) \<longrightarrow> \<not>(N (G \<^bold>\<longrightarrow> E))"
    using L2 L4
    by auto
  lemma L6: "\<not>(N (G \<^bold>\<longrightarrow> E)) \<or>  \<not>\<not>(N (G \<^bold>\<longrightarrow> E))" 
    by simp
  lemma L7: "\<not>(N (G \<^bold>\<longrightarrow> E)) \<longrightarrow> \<not>(P G)" 
    nitpick [user_axioms, show_all, format = 2] sorry
end


end