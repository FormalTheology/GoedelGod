theory AoC
imports Main

begin

typedecl c (*Type for concepts*)

consts contains :: "c\<Rightarrow>c\<Rightarrow>bool" (infix "\<^bold>\<in>" 65)
consts conjunction :: "c\<Rightarrow>c\<Rightarrow>c" (infixr"\<^bold>+" 70)
consts not :: "c\<Rightarrow>c" ("\<^bold>~ _" 75)

definition notcontains :: "c\<Rightarrow>c\<Rightarrow>bool" (infix "\<^bold>\<notin>" 65) where
          "notcontains A B  \<equiv> \<not> (A \<^bold>\<in> B) "
definition equal :: "c \<Rightarrow> c \<Rightarrow> bool" (infixr "\<^bold>=" 40) where
          "equal A B \<equiv> A \<^bold>\<in> B \<and> B \<^bold>\<in> A"
definition notequal :: "c \<Rightarrow> c \<Rightarrow> bool" (infixr "\<^bold>\<noteq>" 40) where
          "notequal A B \<equiv>  \<not> equal A B"
definition possible :: "c \<Rightarrow> bool" ("P _" 74) where
          "P B \<equiv> \<forall>A. B \<^bold>\<notin> A \<^bold>+ \<^bold>~ A" 
(*Note that possible does not mean possible propositions but possible concepts*)
definition disjunction :: "c \<Rightarrow> c \<Rightarrow> c" (infixr "\<^bold>\<or>" 71) where
          "A \<^bold>\<or> B \<equiv>  \<^bold>~ ((\<^bold>~A) \<^bold>+ \<^bold>~B)"
definition indconcept :: "c \<Rightarrow> bool" ("Ind _" 75) where 
          "indconcept A  \<equiv> (P A) \<and> (\<forall>Y. (P (A \<^bold>+ Y)) \<longrightarrow> A \<^bold>\<in> Y)"
definition indexists :: "(c \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<exists>" 10) where(*Lenzen uses different symbol*)
          "\<^bold>\<exists>x. A x  \<equiv> \<exists>(X::c). (Ind X) \<and> A X" 
definition indforall :: "(c \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<^bold>\<forall>" 10) where (*Lenzen uses different symbol*)
          "\<^bold>\<forall>x. A x \<equiv> \<forall>(X::c). (Ind X) \<longrightarrow> A X"

axiomatization where
IDEN2: "\<And>A B. A \<^bold>= B \<longrightarrow> (\<forall>\<alpha>. \<alpha> A \<longleftrightarrow> \<alpha> B)" and
CONT2: "\<And>A B C. A \<^bold>\<in> B \<Longrightarrow> B \<^bold>\<in> C \<Longrightarrow> A \<^bold>\<in> C" and
(*Lenzen uses conjunction here. For computational reasons implications are used*)

CONJ1: "\<And>A B C. A \<^bold>\<in> B \<^bold>+ C \<equiv> A \<^bold>\<in> B \<and> A \<^bold>\<in> C" and
NEG1: "\<And>A. (\<^bold>~ \<^bold>~ A) \<^bold>= A" and
NEG2: "\<And>A B. A \<^bold>\<in> B \<equiv> (\<^bold>~ B) \<^bold>\<in> \<^bold>~ A" and
NEG3: "\<And>A.\<not> (A \<^bold>= \<^bold>~ A)" and
POSS2: "\<And>A B. A \<^bold>\<in> B \<equiv> \<not> P(A \<^bold>+ \<^bold>~ B)" and
MAX: "\<And>B. P B \<Longrightarrow> \<exists>C. \<forall>A. ((B \<^bold>\<in> A) \<longrightarrow> (C \<^bold>\<in> A \<and> C \<^bold>\<notin> \<^bold>~ A))
     \<and> ((B \<^bold>\<in> \<^bold>~ A) \<longrightarrow>(C \<^bold>\<notin> A \<and> C \<^bold>\<in> \<^bold>~ A))
     \<and> ((B \<^bold>\<notin> A \<and> B \<^bold>\<notin> \<^bold>~ A) \<longrightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<or> C \<^bold>\<in> A) \<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))"
(*MAX is an axiom which does not occur in Lenzens paper. 
It turns out to be equivalent to POSS3 and can thus, in principle, be replaced by it *)


lemma CONT1: "A \<^bold>\<in> A" (* This is not needed as an axiom. *)
using CONT2 NEG1 equal_def
by blast

lemma IDEN1: "A \<^bold>= A" (* This is not needed as an axiom. Lenzen explicitly lists it as one.*)
by(simp add: CONT1 equal_def)

lemma equal_sym: "A \<^bold>= B \<equiv> B \<^bold>= A" (*As far as i can tell: we don't need this*)
using equal_def
by smt

lemma CONJ2: "A \<^bold>+ A \<^bold>= A"
using CONJ1 CONT1 equal_def
by auto

lemma CONJ3: "A \<^bold>+ B \<^bold>= B \<^bold>+ A"
using CONJ1 CONT1 equal_def
by auto

lemma CONJ4: "A \<^bold>+ B \<^bold>\<in> A"
using CONJ1 CONT1 by auto

lemma CONJ5: "A \<^bold>+ B \<^bold>\<in> B"
using CONJ1 CONT1
by auto

lemma NEG4: "A \<^bold>= B \<Longrightarrow> (A \<^bold>\<noteq> \<^bold>~B)" 
by (meson IDEN2 NEG3 notequal_def)

lemma NEG5: "P A \<Longrightarrow> (A \<^bold>\<notin> \<^bold>~ A)"
by(simp add: CONJ1 CONT1 possible_def notcontains_def)

lemma NEG6: "P A \<Longrightarrow> A \<^bold>\<in> B \<Longrightarrow> (A \<^bold>\<notin> \<^bold>~ B)"
by(simp add: CONJ1 possible_def notcontains_def)

lemma POSS1: "A \<^bold>\<in> B \<Longrightarrow> P(A) \<Longrightarrow> P(B)"
using CONT2 possible_def notcontains_def
by blast
(*Lenzen uses conjunction, for computational purposes we use implication*)

lemma NEG7: "(A \<^bold>+ \<^bold>~ A) \<^bold>\<in> B" sledgehammer[remote_leo2, verbose]
using CONJ4 CONT1 POSS1 POSS2 by blast
(*Lenzen perhaps thinks this should not be a theorem (p.14).
It is not clear whether this is a mistake on Lenzens part or if it follows
out of some extensional principle where Lenzen wants intensionality.*)

lemma DISJ1: "A \<^bold>\<in> (A \<^bold>\<or> B)"
by(metis CONJ3 CONJ4 NEG2 POSS1 POSS2 disjunction_def equal_def)

lemma DISJ2: "B \<^bold>\<in> (A \<^bold>\<or> B)"
by(metis CONJ3 CONJ5 NEG2 POSS1 POSS2 disjunction_def equal_def)

lemma DISJ3: "A \<^bold>\<in> C \<Longrightarrow> B \<^bold>\<in> C \<Longrightarrow> (A \<^bold>\<or> B) \<^bold>\<in> C"
proof -
fix A :: c and B :: c and C :: c
assume a1: "A \<^bold>\<in> C"
assume a2: "B \<^bold>\<in> C"
have f3: "(\<^bold>~ C) \<^bold>\<in> \<^bold>~ A"
  using a1
  by (metis NEG2)
have f4: "(\<^bold>~ C) \<^bold>\<in> \<^bold>~ B"
  using a2
  by (metis NEG2)
have "(\<^bold>~ C) \<^bold>\<in> (\<^bold>~ A) \<^bold>+ (\<^bold>~ B)"
  using f3 f4
  by (simp add: CONJ1)
thus "A \<^bold>\<or> B \<^bold>\<in> C"
  by(metis CONJ3 POSS1 POSS2 disjunction_def equal_def)
qed
(*Lenzen uses conjunction, for computational purposes we use implication*)


lemma cont3: "A \<^bold>\<in> B \<longleftrightarrow> (\<exists>Y. A \<^bold>= (B \<^bold>+ Y))"
using CONJ1 CONT1 equal_def
by blast
(*used for computation reasons, since Isabelle is not able to show
CONT3 in one step; at least on our machines*)

lemma CONT3: "A \<^bold>\<in> B \<equiv> (\<exists>Y. A \<^bold>= (B \<^bold>+ Y))"
by (simp add: cont3)

lemma CONJ6: "\<exists>Y. Y \<^bold>+ A \<^bold>\<in> B"
using CONJ1 CONT1
by blast

lemma CONJ7: "\<exists>Y. \<exists>Z. Y  \<^bold>+  A  \<^bold>=  Z  \<^bold>+  B"
using CONJ3
by blast

lemma NEG8: "A \<^bold>\<notin> B \<equiv> (\<exists>Y. (P(Y  \<^bold>+  A)) \<and> Y \<^bold>+ A \<^bold>\<in> \<^bold>~ B)"
by(smt CONJ3 CONJ5 CONT2 NEG6 POSS1 POSS2 equal_def notcontains_def)

lemma CONT4: "A \<^bold>\<in> B \<equiv> (\<forall>Y. Y \<^bold>\<in> A \<longrightarrow> Y \<^bold>\<in> B)"
by(smt CONT1 CONT2)

lemma CONT5: "A \<^bold>\<notin> B \<equiv> (\<forall>Y. A \<^bold>\<noteq> Y \<^bold>+ B)"
by(smt CONJ1 CONT1 equal_def notcontains_def notequal_def)

lemma IND1: "(Ind A) \<equiv> (\<forall>Y. (A \<^bold>\<in> \<^bold>~ Y) \<longleftrightarrow> A \<^bold>\<notin> Y)"
proof -
have "(\<forall>Y. (A \<^bold>\<in> \<^bold>~ Y) \<longleftrightarrow> A \<^bold>\<notin> Y) \<Longrightarrow> (Ind A)"
  by(metis CONJ1 CONJ4 CONT4 indconcept_def notcontains_def possible_def)
moreover have "(Ind A) \<Longrightarrow> (\<forall>Y. (A \<^bold>\<in> \<^bold>~ Y) \<longleftrightarrow> A \<^bold>\<notin> Y)"
  using NEG6 POSS2 indconcept_def notcontains_def
  by auto
ultimately show "(Ind A) \<equiv> (\<forall>Y. (A \<^bold>\<in> \<^bold>~ Y) \<longleftrightarrow> A \<^bold>\<notin> Y)"
  by smt
qed

lemma NEG9: "(Ind A) \<Longrightarrow> A \<^bold>\<notin> B \<Longrightarrow> A \<^bold>\<in> \<^bold>~ B"
by(simp add: IND1)

lemma POSS3: "P B \<equiv> \<^bold>\<exists>X. X \<^bold>\<in> B" 
proof -
have f1:"P B \<Longrightarrow> \<^bold>\<exists>X. X \<^bold>\<in> B" 
  proof -
  {
  assume a1: "P B"
  have "\<exists>C. \<forall>A. ((B \<^bold>\<in> A) \<longrightarrow> (C \<^bold>\<in> A \<and> C \<^bold>\<notin> \<^bold>~ A))
    \<and> ((B \<^bold>\<in> \<^bold>~ A) \<longrightarrow> (C \<^bold>\<notin> A \<and> C \<^bold>\<in> \<^bold>~ A))
    \<and> ((B \<^bold>\<notin> A \<and> B \<^bold>\<notin> \<^bold>~ A) \<longrightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<or> C \<^bold>\<in> A) \<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))"
    by(simp add: a1 MAX)
  then obtain C where o1: "\<forall>A. ((B \<^bold>\<in> A) \<longrightarrow> (C \<^bold>\<in> A \<and> C \<^bold>\<notin> \<^bold>~ A))
    \<and> ((B \<^bold>\<in> \<^bold>~ A) \<longrightarrow>(C \<^bold>\<notin> A \<and> C \<^bold>\<in> \<^bold>~ A))
    \<and> ((B \<^bold>\<notin> A \<and> B \<^bold>\<notin> \<^bold>~ A) \<longrightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<or> C \<^bold>\<in> A) \<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))"
    by blast
  have f2: "P C"
    using o1 CONJ4 POSS1 POSS2 notcontains_def
    by blast
  have "\<forall>Y. (P (C \<^bold>+ Y)) \<longrightarrow> C \<^bold>\<in> Y"
    using o1 CONJ4 CONJ5 CONT2 NEG6 notcontains_def
    by blast
  thus ?thesis
    using CONT1 indconcept_def indexists_def o1 possible_def f2
    by auto
  }
  qed
have "\<^bold>\<exists>x. x \<^bold>\<in> B \<Longrightarrow> P B"
  using POSS1 indconcept_def indexists_def
  by auto
with f1 show "P B \<equiv> \<^bold>\<exists>x. x \<^bold>\<in> B"
  by linarith
qed
(*As a side note: It follows from this that everything that is a non-contradictory 
concept sans (non-)existence predicate does in fact exist.
So this axiomatization implies flying elephants  *)
(*Also note that MAX is used in this proof*)


lemma CONT5: "B \<^bold>\<in> C \<equiv> \<^bold>\<forall>X. (X \<^bold>\<in> B) \<longrightarrow> X \<^bold>\<in> C"
proof -
have "B \<^bold>\<in> C \<Longrightarrow> \<^bold>\<forall>X. (X \<^bold>\<in> B) \<longrightarrow> X \<^bold>\<in> C"
  using CONT2 indforall_def
  by blast
moreover have "\<^bold>\<forall>X. (X \<^bold>\<in> B) \<longrightarrow> X \<^bold>\<in> C \<Longrightarrow> B \<^bold>\<in> C"
  proof -
  assume a1: "\<^bold>\<forall>X. (X \<^bold>\<in> B) \<longrightarrow> X \<^bold>\<in> C"
    {
    assume a1: " B \<^bold>\<notin> C"
    hence "\<exists>A. B \<^bold>\<notin> A \<and> C \<^bold>\<in> A"
      using CONT1
      by blast
    then obtain A where o1: "B \<^bold>\<notin> A \<and> C \<^bold>\<in> A"
      by blast
    hence "B \<^bold>\<notin> A"
      by simp
    hence "(B \<^bold>\<in> \<^bold>~ A) \<or> (B \<^bold>\<notin> A \<and> B \<^bold>\<notin> A)"
      by simp
    hence "\<exists>E. E \<^bold>\<in> B \<and> (E \<^bold>\<in> \<^bold>~ A) \<and> (P E)"
      using CONJ4 CONJ5 POSS2 notcontains_def o1
      by blast
    then obtain E where o2: "E \<^bold>\<in> B \<and> (E \<^bold>\<in> \<^bold>~ A) \<and> (P E)"
      by blast
    hence "P E"
      by simp
    hence "\<exists>C. \<forall>A. ((E \<^bold>\<in> A) \<longrightarrow> (C \<^bold>\<in> A \<and> C \<^bold>\<notin> \<^bold>~ A))
      \<and> ((E \<^bold>\<in> \<^bold>~ A) \<longrightarrow> (C \<^bold>\<notin> A \<and> C \<^bold>\<in> \<^bold>~ A))
      \<and> ((E \<^bold>\<notin> A \<and> E \<^bold>\<notin> \<^bold>~ A) \<longrightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<or> C \<^bold>\<in> A) \<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))"
      by(rule MAX)
    then obtain D where o3: "\<forall>A. ((E \<^bold>\<in> A) \<longrightarrow> (D \<^bold>\<in> A \<and> D \<^bold>\<notin> \<^bold>~ A))
      \<and> ((E \<^bold>\<in> \<^bold>~ A) \<longrightarrow>(D \<^bold>\<notin> A \<and> D \<^bold>\<in> \<^bold>~ A))
      \<and> ((E \<^bold>\<notin> A \<and> E \<^bold>\<notin> \<^bold>~ A) \<longrightarrow> (((D \<^bold>\<in> \<^bold>~ A) \<or> D \<^bold>\<in> A) \<and> (D \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))"
      by blast
    with o2 have "D \<^bold>\<notin> A"
      by simp
    with o1 have "D \<^bold>\<notin> C" 
      using CONT2 notcontains_def by blast
    moreover have "Ind D"
      by(metis o3 CONJ5 IND1 NEG6 NEG8 POSS1 notcontains_def)
    moreover have "D \<^bold>\<in> B"
      using o2 o3
      by simp
    ultimately have "\<^bold>\<exists>X. \<not> ((X \<^bold>\<in> B) \<longrightarrow> X \<^bold>\<in> C)"
      using indexists_def notcontains_def
      by auto
    hence "\<not> (\<^bold>\<forall>X. (X \<^bold>\<in> B) \<longrightarrow> X \<^bold>\<in> C)"
      by(simp add: indexists_def indforall_def)
    }
  with a1 show ?thesis
    using notcontains_def
    by blast
  qed
ultimately show "B \<^bold>\<in> C \<equiv> \<^bold>\<forall>X. (X \<^bold>\<in> B) \<longrightarrow> X \<^bold>\<in> C"
  by linarith
qed
(*Note that MAX is used in this proof *)

lemma True nitpick[user_axioms, expect=genuine, satisfy] oops 
(*Nitpick finds a model; however it is the "empty assignment". Not sure about nitpicks inner workings
to determine if that is a problem.*)
end