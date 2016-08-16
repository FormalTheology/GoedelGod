theory God
imports AoC

begin
consts E :: "c" ("E!")
consts G :: "c" ("G")
consts NESS :: "bool \<Rightarrow> bool" (*emulates the box operator; very skeptical about that.*)

axiomatization where
GOD3: "\<forall>X. X \<^bold>\<in> G \<longleftrightarrow> (NESS (X \<^bold>\<in> E!))" and
M: "NESS X \<Longrightarrow> X" (*Only the T-Axiom is necessary for the proof to work.*)

theorem GOD2: "(P G) \<longrightarrow> G \<^bold>\<in> E!"
using CONT1 GOD3 M by blast

theorem GOD1: "P G" nitpick[user_axioms] oops
(*Nitpick finds a countermodel *)

theorem NOTGOD1: "\<not> P G" nitpick[user_axioms] oops
(*Nitpick also finds a countermodel for the opposite claim*)


(*However: Gods existence can still be proven. But this is !not! part of Lenzens paper.*)
theorem GOD: "G \<^bold>\<in> E!" using CONT1 GOD3 M by blast
(* To see why this is true, consider: Either P G then by modus ponens and GOD2 god exists.
Or \<not>(P G) then the concept contains (an analogon to ex falso quodlibet)
 every other concept therefore also the existence concept. In Isabelle: 
theorem exfalso: " (\<not> (P A)) \<Longrightarrow> (A \<^bold>\<in> B) " using  CONJ4 POSS1 POSS2  by blast
*)


end