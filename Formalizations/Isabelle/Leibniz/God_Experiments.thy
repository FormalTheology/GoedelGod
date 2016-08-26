theory God_Experiments
imports AoC

begin
consts 
 E :: "c" ("E")  
 G :: "c" ("G")

declare [[ smt_solver = cvc4]]

context (* Short proof with axiom "N(G \<^bold>\<longrightarrow> E)" *)
 assumes 
  NG: "N(G \<^bold>\<longrightarrow> E)"
 begin
  lemma L10: "(P G) \<longrightarrow> (G \<^bold>\<sqsupset> E)" 
    by (smt CONJ1 CONJ4 CONJ5 CONT2 MAX NEG8 NG necessary_def POSS1 POSS2 disjunction_def 
            implication_def notcontains_def)

  (* This shows that the assumption of possibility is not needed. *)
  lemma L11: "(G \<^bold>\<sqsupset> E)" 
    by (metis CONT2 NEG1 NG necessary_def POSS1 POSS2 disjunction_def equal_def implication_def)

  (* Necessity of concept implication is equivalent to concept containment *)
  lemma L12: "\<forall>X.\<forall>Y.((N(X \<^bold>\<longrightarrow> Y)) \<longleftrightarrow> (X \<^bold>\<sqsupset> Y))"
    by (metis CONT2 NEG1 necessary_def POSS1 POSS2 disjunction_def equal_def implication_def)

  lemma ImpossibleObjectsExist: "\<forall>X. \<not> (P X) \<longrightarrow> (X \<^bold>\<sqsupset>  E)"
  using CONJ4 POSS1 POSS2 by blast

  lemma Unicorn: "\<forall>X. (P(X \<^bold>+ E)) \<longrightarrow> (X \<^bold>\<sqsupset> E)" nitpick[user_axioms] oops

 end

context (* Short proof attempt with axiom (N G) *)
 assumes 
  NG: "N G"
 begin
  lemma L10': "(P G) \<longrightarrow> (G \<^bold>\<sqsupset> E)" 
    nitpick[user_axioms, show_all, format = 2] oops
 end


