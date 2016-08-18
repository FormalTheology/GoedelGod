theory God
imports AoC

begin
consts E :: "c" ("E!")
consts G :: "c" ("G")

definition NESS :: "c \<Rightarrow> bool" where "NESS A \<equiv> \<not> P (\<^bold>~ A) "
definition PE1 :: "bool" where "PE1 \<equiv> \<forall>X. (\<not> (X \<^bold>\<in> E!)) \<longrightarrow> P (\<^bold>~ X)"
definition PE2 :: "bool" where "PE2 \<equiv> \<forall>X. (\<not> (X \<^bold>\<in> E!)) \<longrightarrow> \<not> P X"

axiomatization where
NG: "NESS G" and
PE1: "PE1"

lemma PE2ImpPE1: "PE2 \<Longrightarrow> PE1" by (meson CONJ5 NEG6 PE1_def PE2_def POSS2)
lemma PE1ImpPE2: "PE1 \<Longrightarrow> PE2" by (meson PE1 CONJ4 POSS1 POSS2 PE1_def NEG2 NESS_def NG PE2_def)

theorem GOD2: "(P G) \<longrightarrow> (G \<^bold>\<in> E!)" using PE1 PE1ImpPE2 PE2_def by auto
(*
proof -
{
  (*(i) By hypothesis, the necessary being doesn‘t exist.*)
  assume i: "\<not> G \<^bold>\<in> E"
  (* (ii) Whenever something doesn’t exist, it possibly doesn’t exist. *)
  have ii: "\<forall>X. (\<not> (X \<^bold>\<in> E!)) \<longrightarrow> P (X)" by (simp add: POSS2)
  (* (iii) Whenever something possibly doesn’t exist, it is falsely maintained to be impossible not to exist. *)
  have iii: "\<forall>X. P (X \<^bold>+ \<^bold>~ E!) \<longrightarrow> \<not> \<not> P (X \<^bold>+ \<^bold>~ E!)" by simp
  (* (iv) Whenever something is falsely maintained to be impossible not to exist,
then it is falsely maintained to be necessary. (For necessary is what is
impossible not to exist.) *)
  have iv: "\<forall>X. \<not> \<not> P (X \<^bold>+ \<^bold>~ E!) \<longrightarrow> \<not> NESS ()"
  (* (v) Therefore the necessary being is falsely maintained to be necessary. *)
  
  (* (vi) This conclusion is either true or false. *)
  
  (* (vii) If it is true, it follows that the necessary being contains a contradiction,
or is impossible, because contradictory assertions have been proved about it,
namely that it is not necessary. For a contradictory conclusion can only be
shown about a thing which implies a contradiction. *)
  
  (* (viii) If it is false, necessarily one of the premises must be false. But the only
premise that might be false is the hypothesis saying that the necessary being
doesn’t exist. *)
  
  (* (ix) Hence we conclude that the necessary being either is impossible, or it
exists. *)
  
  (* (x) So if we define GOD as an “Ens a se”, i.e. a being from whose essence
its existence follows, i.e. a necessary being, it follows that GOD, if he is
possible, actually exists. *)
  
}
*)

theorem GOD1: "P G" nitpick[user_axioms, satisfy] oops

theorem NOTGOD1: "\<not> P G" nitpick[user_axioms, satisfy] oops (* Not any more? ... timeout 120 is not enough for my PC*)

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

(* We can prove that unicorns exists 
if it is possible that unicorns might exists. *)

consts uni :: "c" --"being a unicorn"

theorem unicorn:
assumes "P (uni \<^bold>+ E!)"
shows "\<^bold>\<exists>X. X \<^bold>\<in> (uni \<^bold>+ E!)"
using POSS3 assms
by auto

(* Furthermore, we can prove that unicorns exists
if being a unicorn is possible for non-existing concepts
under the assumption that being a unicorn does not include
being non-existing. *)

theorem unicorn2:
assumes "P uni" and "uni \<^bold>\<notin> \<^bold>~ E!"
shows "\<^bold>\<exists>X. X \<^bold>\<in> (uni \<^bold>+ E!)"
proof -
have "\<exists>C. \<forall>A. ((uni \<^bold>\<in> A) \<longrightarrow> (C \<^bold>\<in> A \<and> C \<^bold>\<notin> \<^bold>~ A))
     \<and> ((uni \<^bold>\<in> \<^bold>~ A) \<longrightarrow>(C \<^bold>\<notin> A \<and> C \<^bold>\<in> \<^bold>~ A))
     \<and> ((uni \<^bold>\<notin> A \<and> uni \<^bold>\<notin> \<^bold>~ A) \<longrightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<or> C \<^bold>\<in> A) \<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))"
  using assms MAX
  by simp
hence "\<exists>C. C \<^bold>\<in> (uni \<^bold>+ E!) \<and> P C"
  by (smt CONJ1 CONJ5 IDEN2 NEG1 NEG8 assms(2))
then obtain X where "X \<^bold>\<in> (uni \<^bold>+ E!) \<and> P X"
  by blast
thus ?thesis
  using POSS1 POSS3
  by auto
qed


end