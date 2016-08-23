theory God_D_Experiments
imports AoC_Implication

begin
consts 
 E :: "c" ("E")  
 G :: "c" ("G")

definition N :: "c \<Rightarrow> bool" where "N A \<equiv> \<not> P (\<^bold>~ A) "

declare [[ smt_solver = cvc4]]

context (* Short proof with axiom "N(G \<^bold>\<longrightarrow> E)" *)
 assumes 
  NG: "N(G \<^bold>\<longrightarrow> E)"
 begin
  lemma L10: "(P G) \<longrightarrow> (G \<^bold>\<sqsupset> E)" 
    by (smt CONJ1 CONJ4 CONJ5 CONT2 MAX NEG8 NG N_def POSS1 POSS2 disjunction_def 
            implication_def notcontains_def)

  (* This shows that the assumption of possibility is not needed. *)
  lemma L11: "(G \<^bold>\<sqsupset> E)" 
    by (metis CONT2 NEG1 NG N_def POSS1 POSS2 disjunction_def equal_def implication_def)

  (* Necessity of concept implication and concept containment *)
  lemma L12: "\<forall>X.\<forall>Y.(N(Y \<^bold>\<longrightarrow> Y) \<longrightarrow> (X \<^bold>\<sqsupset> Y))"
    nitpick [user_axioms, show_all, format = 2] sorry  --{* Countermodel *}
  lemma L13: "\<forall>X.\<forall>Y.(X \<^bold>\<sqsupset> Y) \<longrightarrow>  (N(Y \<^bold>\<longrightarrow> Y) )"
    by (smt CONT2 DISJ1 DISJ2 NEG2 NEG5 N_def implication_def notcontains_def)

 
 end

context (* Short proof attempt with axiom (N G) *)
 assumes 
  NG: "N G"
 begin
  lemma L10': "(P G) \<longrightarrow> (G \<^bold>\<sqsupset> E)" 
    nitpick[user_axioms, show_all, format = 2] oops

 end


