theory GodKripke
imports AoCKripke

begin

consts E :: "c" ("E!")
consts G :: "c" ("G")

axiomatization where
GOD3: "\<lfloor>\<^bold>\<forall>X. X \<^bold>\<in> G \<^bold>\<leftrightarrow> (\<^bold>\<box>(X \<^bold>\<in> E!))\<rfloor>" and
M: T_ax


theorem GOD2: "\<lfloor>(P G) \<^bold>\<rightarrow> G \<^bold>\<in> E!\<rfloor>"
using CONT1 GOD3 M by blast

theorem GOD1: "\<lfloor>P G\<rfloor>" nitpick[user_axioms] oops
(*P G is no theorem. nitpick finds a countermodel.*)

theorem NOTGOD1: "\<lfloor>\<^bold>\<not> P G\<rfloor>" nitpick[user_axioms] oops
(*Nitpick also finds a countermodel for the opposite claim*)



(*However: Gods existence can still be proven. But this is !not! part of Lenzens paper.*)
theorem GOD: "\<lfloor>G \<^bold>\<in> E!\<rfloor>" using CONT1 GOD3 M by blast
(* To see why this is true, consider: Either P G then by modus ponens and GOD2 god exists.
Or \<not>(P G) then the concept contains (an analogon to ex falso quodlibet)
 every other concept therefore also the existence concept. In Isabelle:
theorem exfalso:"\<lfloor>(\<^bold>\<not> (P A)) \<^bold>\<rightarrow> (A \<^bold>\<in> B)\<rfloor>" using  CONJ4 POSS1 POSS2  by blast
 *)


end