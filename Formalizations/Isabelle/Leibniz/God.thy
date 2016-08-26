theory God
imports AoC
begin
consts  E :: "c" ("E")   
        G :: "c" ("G")

axiomatization where NG: "N(G \<^bold>\<longrightarrow> E)" and 
  GnotE: "G \<^bold>\<noteq> E" and GnotnotE: "G \<^bold>\<noteq> \<^bold>~E"
                     
(* Nitpick finds a model. Therefore, the axiomatization is consistent. *)
lemma True 
nitpick[user_axioms, show_all, format=2, expect=genuine, satisfy] 
oops 

(* 2)	For whatever doesn’t exist, for it is possible not to exist. *)
lemma L2': "(X \<^bold>\<notin> E) \<longrightarrow> (P (X \<^bold>+ \<^bold>~E))" by (simp add: POSS2 notcontains_def)
(* 3)	For whatever it’s possible not to exist, of it it’s false to say that 
it cannot not exist.  *)
lemma L3': "(P (X \<^bold>+ \<^bold>~E)) \<longrightarrow> \<not>\<not>(P (X \<^bold>+ \<^bold>~E))" by simp
(* 4)	Of whatever it is false to say that it is not possible not to exist, of 
it’s false to say that it is necessary. (For necessary is what cannot not exist.) *)
lemma L4': "\<not>\<not>(P (X \<^bold>+ \<^bold>~E)) \<longrightarrow> \<not>(N (X \<^bold>\<longrightarrow> E))" by (smt CONJ1 CONJ4 CONJ5 CONT2 IDEN2 
  NEG1 necessary_def POSS1 disjunction_def equal_def implication_def) 
(* 5)	Therefore, of the necessary being it’s false to say it is necessary.  *)
lemma L5': "(G \<^bold>\<notin> E) \<longrightarrow> \<not>(N (G \<^bold>\<longrightarrow> E))" using L2' L4' by auto
(* 6)	This conclusion is either true or false.  *)
lemma L6': "\<not>(N (G \<^bold>\<longrightarrow> E)) \<or> \<not>\<not>(N (G \<^bold>\<longrightarrow> E))" by simp
(* 7)	If it is true, it follows that the necessary being contains a contradiction, i.e. 
is impossible, because contradictory assertions have been proved about it, namely that it 
is not necessary. For a contradictory conclusion can only be shown about a thing which 
contains a contradiction.  *)
lemma L7': "\<not>(N (G \<^bold>\<longrightarrow> E)) \<longrightarrow> \<not>(P G)" by (simp add: NG)
(* 8)	If it is false, necessarily one of the premises must be false. But the only premise 
that might be false is the hypothesis that the necessary being doesn’t exist.  *)
lemma L8': "\<not>\<not>(N (G \<^bold>\<longrightarrow> E)) \<longrightarrow> \<not>(G \<^bold>\<notin> E)" using L5' by blast
(* 9)	Hence we conclude that  the necessary being either is impossible, or exists.  *)
lemma L9': "\<not>(P G) \<or> (G \<^bold>\<sqsupset> E)" using L6' L7' L8' notcontains_def by metis
(* 10)	So if we define God as an “Ens a se”, i.e. a being from whose essence its existence 
follows, i.e. a necessary being, it follows that God, if It is possible, actually exists. *)
lemma L10': "(P G) \<longrightarrow> (G \<^bold>\<sqsupset> E)"  using L9' by auto

lemma God: "(G \<^bold>\<sqsupset> E)" using L5' NG notcontains_def by auto

end
