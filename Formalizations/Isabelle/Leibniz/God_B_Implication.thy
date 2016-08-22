theory God_B_Implication
imports AoC_Implication

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
  lemma L4: "\<not>\<not>(P (X \<^bold>+ \<^bold>~E!)) \<longrightarrow> \<not>(N (G \<^bold>\<longrightarrow> E!))"
    using CONJ1 CONJ4 CONJ5 CONT2 IDEN2 NEG1 N_def POSS1 disjunction_def equal_def implication_def POSS2 NG
    by metis
  lemma L5: "\<not>(G \<^bold>\<in> E) \<longrightarrow> \<not>(N (G \<^bold>\<longrightarrow> E!))"
    using L2 L4
    by auto
  lemma L6: "\<not>(N (G \<^bold>\<longrightarrow> E!)) \<or>  \<not>\<not>(N (G \<^bold>\<longrightarrow> E!))" 
    by simp
  lemma L7: "\<not>(N (G \<^bold>\<longrightarrow> E!)) \<longrightarrow> \<not>(P G)" 
    nitpick [user_axioms, show_all, format = 2] sorry
end


(* Nitpick found a counterexample for card c = 2:
  Constants:
    op \<^bold>+ = (\<lambda>x. _)((c\<^sub>1, c\<^sub>1) := c\<^sub>1, (c\<^sub>1, c\<^sub>2) := c\<^sub>1, (c\<^sub>2, c\<^sub>1) := c\<^sub>1, (c\<^sub>2, c\<^sub>2) := c\<^sub>2)
    op \<^bold>\<in> = (\<lambda>x. _)((c\<^sub>1, c\<^sub>1) := True, (c\<^sub>1, c\<^sub>2) := True, (c\<^sub>2, c\<^sub>1) := False, (c\<^sub>2, c\<^sub>2) := True)
    not = (\<lambda>x. _)(c\<^sub>1 := c\<^sub>2, c\<^sub>2 := c\<^sub>1)
    E! = c\<^sub>1
    G = c\<^sub>2 *)

context (* Proof with axiom N(G \<^bold>\<longrightarrow> E!) *)
 assumes 
  NG: "N(G \<^bold>\<longrightarrow> E!)"
 begin
(* 2)	For whatever doesn’t exist, for it is possible not to exist. *)
  lemma L2': "(X \<^bold>\<notin> E!) \<longrightarrow> (P (X \<^bold>+ \<^bold>~E!))"
    by (simp add: POSS2 notcontains_def)
(* 3)	For whatever it’s possible not to exist, 
of it it’s false to say that it cannot not exist.  *)
  lemma L3': "(P (X \<^bold>+ \<^bold>~E!)) \<longrightarrow> \<not>\<not>(P (X \<^bold>+ \<^bold>~E!)) "
    by simp
(* 4)	Of whatever it is false to say that it is not possible not to exist, 
of it’s false to say that it is necessary. 
(For necessary is what cannot not exist.) *)
  lemma L4': "\<not>\<not>(P (X \<^bold>+ \<^bold>~E!)) \<longrightarrow> \<not>(N (X \<^bold>\<longrightarrow> E!))"
    by (smt CONJ1 CONJ4 CONJ5 CONT2 IDEN2 NEG1 N_def POSS1 disjunction_def equal_def implication_def) 
(* 5)	Therefore, of the necessary being it’s false to say it is necessary.  *)
lemma L5': "(G \<^bold>\<notin> E) \<longrightarrow> \<not>(N (G \<^bold>\<longrightarrow> E!))"
    using L2' L4'
    by auto
(* 6)	This conclusion is either true or false.  *)
  lemma L6': "\<not>(N (G \<^bold>\<longrightarrow> E!)) \<or> \<not>\<not>(N (G \<^bold>\<longrightarrow> E!))" 
    by simp
(* 7)	If it is true, it follows that the necessary being contains a contradiction,
i.e. is impossible, because contradictory assertions have been proved about it,
namely that it is not necessary. For a contradictory conclusion can only be shown
about a thing which contains a contradiction.  *)
  lemma L7': "\<not>(N (G \<^bold>\<longrightarrow> E!)) \<longrightarrow> \<not>(P G)" 
    by (simp add: NG)
(* 8)	If it is false, necessarily one of the premises must be false.
But the only premise that might be false is the hypothesis
that the necessary being doesn’t exist.  *)
  lemma L8': "\<not>\<not>(N (G \<^bold>\<longrightarrow> E!)) \<longrightarrow> \<not>(G \<^bold>\<notin> E)" 
    using L5'
    by blast
(* 9)	Hence we conclude that 
the necessary being either is impossible, or exists.  *)
  lemma L9': "\<not>(P G) \<or> (G \<^bold>\<in> E)" 
    using L6' L7' L8' notcontains_def
    by metis
(* 10)	So if we define God as an “Ens a se”,
i.e. a being from whose essence its existence follows,
i.e. a necessary being, it follows that God,
if It is possible, actually exists.  *)
  lemma L10': "(P G) \<longrightarrow> (G \<^bold>\<in> E)" 
    using L9'
    by auto


lemma God: "(G \<^bold>\<in> E!)"
using L5' NG notcontains_def
by auto
(* Note that impossible objects contain any property, therefore any impossible object exists. *)

lemma ImpossibleObjectsExist: "\<forall>X. \<not> P X \<longrightarrow> X \<^bold>\<in> E!"
using CONJ4 L2' POSS1 notcontains_def
by blast

lemma Unicorn: "\<forall>X. P (X \<^bold>+ E!) \<longrightarrow> (X \<^bold>\<in> E!)" nitpick[user_axioms] oops
(* With this notion of possible existence, not all possible objects exist. *)
end
end