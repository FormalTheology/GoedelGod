theory God
imports AoC

begin
consts E :: "c" ("E!")
consts G :: "c" ("G")

axiomatization where
GOD3: "\<forall>X. X \<^bold>\<in> G \<longleftrightarrow> (NESS (X \<^bold>\<in> E!))" and
M: "NESS X \<Longrightarrow> X"

theorem GOD2: "(P G) \<longrightarrow> G \<^bold>\<in> E!"
using CONT1 GOD3 M by blast

theorem GOD1: "P G" nitpick[user_axioms, satisfy] oops

theorem NOTGOD1: "\<not> P G" nitpick[user_axioms, satisfy] oops

(*
GOD1 and its negation are both satisfiable in this logic.
Therefore non of them can be theorems in this logic,
unless one adds more axioms to it. *)

theorem GOD: "G \<^bold>\<in> E!" using CONT1 GOD3 M by blast

(*
Caution: Leibniz logic states all concepts for impossible objects.
This can be seen in:
theorem assumes "\<lfloor>\<^bold>\<not> P A\<rfloor>" shows "\<lfloor>A \<^bold>\<in> B\<rfloor>"
using CONJ4 POSS1 POSS2 assms
by blast
*)

end