theory AoCKripke
imports Main
(*Leibniz Algebra of Concepts fused with Kripkestyle modal logic*)
begin

typedecl c
typedecl i
type_synonym \<sigma> = "(i\<Rightarrow>bool)"

consts r :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70)
consts contains :: "c \<Rightarrow> c \<Rightarrow> \<sigma>" (infix "\<^bold>\<in>" 65)
consts conjunction :: "c \<Rightarrow> c \<Rightarrow> c" (infixr"\<^bold>+" 70)
consts not :: "c \<Rightarrow> c" ("\<^bold>~ _" 75)

abbreviation mnot :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)"
abbreviation mnegpred :: "(c\<Rightarrow>\<sigma>)\<Rightarrow>(c\<Rightarrow>\<sigma>)" ("\<^sup>\<not>_"[52]53)
  where "\<^sup>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>\<Phi>(x)(w)"
abbreviation mand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51)
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"
abbreviation mor :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50)
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"
abbreviation mimp :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49)
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"
abbreviation mequ :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48)
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"
abbreviation mforall :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")
  where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
abbreviation mforallB :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9)
  where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"
abbreviation mexists :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>")
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
abbreviation mexistsB :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9)
  where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"
abbreviation mbox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>_"[52]53)
  where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. w r v \<longrightarrow> \<phi>(v)"
abbreviation mdia :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>_"[52]53)
  where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. w r v \<and> \<phi>(v)"

abbreviation valid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"
abbreviation M
  where "M \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>"
abbreviation T_ax :: bool
 where "T_ax  \<equiv> \<lfloor>M\<rfloor>"

definition notcontains :: "c\<Rightarrow>c\<Rightarrow>\<sigma>" (infix "\<^bold>\<notin>" 65) where "notcontains A B  \<equiv> \<^bold>\<not> (A \<^bold>\<in> B)"
definition equal :: "c \<Rightarrow> c \<Rightarrow> \<sigma>" (infixr "\<^bold>=" 40) where "equal A B \<equiv> (A \<^bold>\<in> B) \<^bold>\<and> (B \<^bold>\<in> A)"
definition notequal :: "c \<Rightarrow> c \<Rightarrow> \<sigma>" (infixr "\<^bold>\<noteq>" 40) where "notequal A B \<equiv> \<^bold>\<not> equal A B"
definition possible :: "c \<Rightarrow> \<sigma>" ("P _" 74) where "P B \<equiv> \<^bold>\<forall>A. B \<^bold>\<notin> A \<^bold>+ \<^bold>~ A"
(*Note that possible does not mean possible propositions but possible concepts*)

definition disjunction :: "c \<Rightarrow> c \<Rightarrow> c" (infixr "\<^bold>|" 71) where "A \<^bold>| B \<equiv>  \<^bold>~ ((\<^bold>~A) \<^bold>+ \<^bold>~B)"
definition implication :: "c \<Rightarrow> c \<Rightarrow> c" (infixr "\<^bold>\<longrightarrow>" 73) where "A \<^bold>\<longrightarrow> B \<equiv> (\<^bold>~A) \<^bold>| B"
definition indconcept :: "c \<Rightarrow> \<sigma>" ("Ind _" 75) where "indconcept A \<equiv> (P A) \<^bold>\<and> (\<^bold>\<forall>Y. (P (A \<^bold>+ Y)) \<^bold>\<rightarrow> A \<^bold>\<in> Y)"
definition indexists :: "(c \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (binder "\<^bold>\<Or>" 10) where "\<^bold>\<Or>x. A x  \<equiv> \<^bold>\<exists>(X::c). (Ind X) \<^bold>\<and> A X"
definition indforall :: "(c \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  (binder "\<^bold>\<And>" 10) where "\<^bold>\<And>x. A x \<equiv> \<^bold>\<forall>(X::c). (Ind X) \<^bold>\<rightarrow> A X"

axiomatization where
IDEN2: "\<lfloor>(A \<^bold>= B) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<alpha> A \<^bold>\<leftrightarrow> \<alpha> B)\<rfloor>" and
CONT2: "\<lfloor>A \<^bold>\<in> B \<^bold>\<rightarrow> B \<^bold>\<in> C \<^bold>\<rightarrow> A \<^bold>\<in> C\<rfloor>" and
(*Lenzen uses conjunction here. For computational reasons implication is used*)

CONJ1: "\<lfloor>A \<^bold>\<in> B \<^bold>+ C \<^bold>\<leftrightarrow> A \<^bold>\<in> B \<^bold>\<and> A \<^bold>\<in> C\<rfloor>" and
NEG1: "\<lfloor>(\<^bold>~ \<^bold>~ A) \<^bold>= A\<rfloor>" and
NEG2: "\<lfloor>A \<^bold>\<in> B \<^bold>\<leftrightarrow> (\<^bold>~ B) \<^bold>\<in> \<^bold>~ A\<rfloor>" and
NEG3: "\<lfloor>\<^bold>\<not> (A \<^bold>= \<^bold>~ A)\<rfloor>" and (*Lenzen seems to think this is a theorem. It isn't.*)
POSS2: "\<lfloor>A \<^bold>\<in> B \<^bold>\<leftrightarrow> \<^bold>\<not> P(A \<^bold>+ \<^bold>~ B)\<rfloor>" and
MAX: "\<lfloor>(P B) \<^bold>\<rightarrow> (\<^bold>\<exists>C. \<^bold>\<forall>A. ((B \<^bold>\<in> A) \<^bold>\<rightarrow> (C \<^bold>\<in> A \<^bold>\<and> C \<^bold>\<notin> \<^bold>~ A)) \<^bold>\<and> ((B \<^bold>\<in> \<^bold>~ A) \<^bold>\<rightarrow> (C \<^bold>\<notin> A \<^bold>\<and> C \<^bold>\<in> \<^bold>~ A)) \<^bold>\<and> ((B \<^bold>\<notin> A \<^bold>\<and> B \<^bold>\<notin> \<^bold>~ A) \<^bold>\<rightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<^bold>\<or> C \<^bold>\<in> A) \<^bold>\<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A))))\<rfloor>"
(*MAX is an axiom which does not occur in Lenzens paper. 
It turns out to be equivalent to POSS3 and can thus, in principle, be replaced by it *)


lemma CONT1: "\<lfloor>A \<^bold>\<in> A\<rfloor>" using CONT2 NEG1 equal_def by meson (* Not needed as an Axiom *)

lemma IDEN1: "\<lfloor>A \<^bold>= A\<rfloor>" by(simp add: CONT1 equal_def) (* This is not needed as an axiom. Lenzen explicitly lists it as one.*)

lemma CONJ2: "\<lfloor>A \<^bold>+ A \<^bold>= A\<rfloor>" using CONJ1 CONT1 equal_def by meson

lemma CONJ3: "\<lfloor>A \<^bold>+ B \<^bold>= B \<^bold>+ A\<rfloor>" using CONJ1 CONT1 equal_def by meson

lemma CONJ4: "\<lfloor>A \<^bold>+ B \<^bold>\<in> A\<rfloor>" using CONJ1 CONT1 by meson

lemma CONJ5: "\<lfloor>A \<^bold>+ B \<^bold>\<in> B\<rfloor>" using CONJ1 CONT1 by meson

lemma NEG4: "\<lfloor>(A \<^bold>= B) \<^bold>\<rightarrow> (\<^bold>\<not> (A \<^bold>= \<^bold>~ B))\<rfloor>" using CONT2 NEG3 equal_def by meson

lemma NEG5: "\<lfloor>(P A) \<^bold>\<rightarrow> (A \<^bold>\<notin> \<^bold>~ A)\<rfloor>" by(simp add: CONJ1 CONT1 possible_def notcontains_def)

lemma NEG6: "\<lfloor>(P A) \<^bold>\<and> (A \<^bold>\<in> B) \<^bold>\<rightarrow> \<^bold>\<not> (A \<^bold>\<in> \<^bold>~ B)\<rfloor>" by(simp add: CONJ1 possible_def notcontains_def)

lemma POSS1: "\<lfloor>A \<^bold>\<in> B \<^bold>\<and> (P A) \<^bold>\<rightarrow> (P B)\<rfloor>" using CONT2 possible_def notcontains_def by meson

lemma NEG7: "\<lfloor>(A \<^bold>+ \<^bold>~ A) \<^bold>\<in> B\<rfloor>" by(meson CONJ4 CONJ5 NEG6 POSS1 POSS2)
(*Lenzen perhaps thinks this should not be a theorem (p.14).
It is not clear whether this is a mistake on Lenzens part or if it follows
out of some extensional principle where Lenzen wants intensionality.*)

lemma DISJ1: "\<lfloor>A \<^bold>\<in> (A \<^bold>| B)\<rfloor>" by(metis CONJ3 CONJ4 NEG2 POSS1 POSS2 disjunction_def equal_def)

lemma DISJ2: "\<lfloor>B \<^bold>\<in> (A \<^bold>| B)\<rfloor>" by(metis (mono_tags, lifting) CONJ3 CONJ5 NEG2 POSS1 POSS2 disjunction_def equal_def)

lemma DISJ3: "\<lfloor>A \<^bold>\<in> C \<^bold>\<and> B \<^bold>\<in> C \<^bold>\<rightarrow> (A \<^bold>| B) \<^bold>\<in> C\<rfloor>"
proof -
{
  fix w :: i
  {
    assume "((\<^bold>~ C) \<^bold>\<in> (\<^bold>~ A) \<^bold>\<and> (\<^bold>~ C) \<^bold>\<in> \<^bold>~ B) w"
    then have "\<exists>c. (c \<^bold>\<in> (\<^bold>~ A) \<^bold>+ (\<^bold>~ B) \<^bold>\<and> (\<^bold>~ c) \<^bold>\<in> C) w" by (meson CONJ1 NEG1 equal_def)
    then have "(C \<^bold>\<notin> A \<^bold>\<or> C \<^bold>\<notin> B \<^bold>\<or> A \<^bold>| B \<^bold>\<in> C) w" by (metis CONT2 NEG2 disjunction_def)
  }
  then have "((\<^bold>~ C) \<^bold>\<notin> (\<^bold>~ A) \<^bold>\<or> (\<^bold>~ C) \<^bold>\<notin> (\<^bold>~ B) \<^bold>\<or> A \<^bold>| B \<^bold>\<in> C) w" by (smt CONJ1 CONT2 NEG1 NEG2 disjunction_def equal_def notcontains_def)
}
thus ?thesis using NEG2 notcontains_def by auto
qed

lemma CONT3: "\<lfloor>(A \<^bold>\<in> B) \<^bold>\<leftrightarrow> (\<^bold>\<exists>Y. A \<^bold>= (B \<^bold>+ Y))\<rfloor>" using CONJ1 CONT1 equal_def by meson

lemma CONJ6: "\<lfloor>\<^bold>\<exists>Y. Y \<^bold>+ A \<^bold>\<in> B\<rfloor>" using CONJ1 CONT1 by blast

lemma CONJ7: "\<lfloor>\<^bold>\<exists>Y. \<^bold>\<exists>Z. Y \<^bold>+ A \<^bold>= Z \<^bold>+ B\<rfloor>" using CONJ3 by blast

lemma NEG8: "\<lfloor>A \<^bold>\<notin> B \<^bold>\<leftrightarrow> (\<^bold>\<exists>Y. (P(Y \<^bold>+ A)) \<^bold>\<and> Y \<^bold>+ A \<^bold>\<in> \<^bold>~ B)\<rfloor>"
proof -
{
  fix w :: i
  {
    assume "(A \<^bold>\<notin> B) w"
    hence "(\<^bold>\<exists>Y. (P(Y \<^bold>+ A)) \<^bold>\<and> Y \<^bold>+ A \<^bold>\<in> \<^bold>~ B) w" by (meson CONJ3 CONJ4 CONT2 NEG7 POSS2 equal_def notcontains_def possible_def)
  }
  moreover
  {
    assume "(\<^bold>\<exists>Y. (P(Y \<^bold>+ A)) \<^bold>\<and> Y \<^bold>+ A \<^bold>\<in> \<^bold>~ B) w"
    hence "(A \<^bold>\<notin> B) w" by (meson CONJ5 CONT2 NEG6 notcontains_def)
  }
  ultimately
  have "(A \<^bold>\<notin> B \<^bold>\<leftrightarrow> (\<^bold>\<exists>Y. (P(Y \<^bold>+ A)) \<^bold>\<and> Y \<^bold>+ A \<^bold>\<in> \<^bold>~ B)) w" by blast
}
thus ?thesis by simp
qed

lemma CONT4: "\<lfloor>A \<^bold>\<in> B \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. Y \<^bold>\<in> A \<^bold>\<rightarrow> Y \<^bold>\<in> B)\<rfloor>" by(smt CONT1 CONT2)

lemma CONT5: "\<lfloor>A \<^bold>\<notin> B \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. A \<^bold>\<noteq> Y \<^bold>+ B)\<rfloor>" by(smt CONJ1 CONT1 equal_def notcontains_def notequal_def)

lemma IND1: "\<lfloor>(Ind A) \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. (A \<^bold>\<in> \<^bold>~ Y) \<^bold>\<leftrightarrow> A \<^bold>\<notin> Y)\<rfloor>"
proof -
have "\<lfloor>(\<^bold>\<forall>Y. (A \<^bold>\<in> \<^bold>~ Y) \<^bold>\<leftrightarrow> (A \<^bold>\<notin> Y)) \<^bold>\<rightarrow> (Ind A)\<rfloor>" by (metis (full_types) CONJ1 CONJ4 CONT4 indconcept_def notcontains_def possible_def)
moreover
have "\<lfloor>(Ind A) \<^bold>\<rightarrow> (\<^bold>\<forall>Y. (A \<^bold>\<in> \<^bold>~ Y) \<^bold>\<leftrightarrow> A \<^bold>\<notin> Y)\<rfloor>" using NEG6 POSS2 indconcept_def notcontains_def by auto
ultimately
show "\<lfloor>(Ind A) \<^bold>\<leftrightarrow> (\<^bold>\<forall>Y. (A \<^bold>\<in> \<^bold>~ Y) \<^bold>\<leftrightarrow> A \<^bold>\<notin> Y)\<rfloor>" by smt
qed

lemma NEG9: "\<lfloor>(Ind A) \<^bold>\<and> A \<^bold>\<notin> B \<^bold>\<rightarrow> A \<^bold>\<in> \<^bold>~ B\<rfloor>" by (simp add: IND1)

lemma POSS3: "\<lfloor>(P B) \<^bold>\<leftrightarrow> (\<^bold>\<Or>x. x \<^bold>\<in> B)\<rfloor>"
proof -
have f1:"\<lfloor>(P B) \<^bold>\<rightarrow> (\<^bold>\<Or>x. x \<^bold>\<in> B)\<rfloor>"
  proof -
  {
    fix w::i
    assume a1: "(P B) w"
    have "(\<^bold>\<exists>C. \<^bold>\<forall>A. ((B \<^bold>\<in> A) \<^bold>\<rightarrow> (C \<^bold>\<in> A \<^bold>\<and> C \<^bold>\<notin> \<^bold>~ A)) \<^bold>\<and> ((B \<^bold>\<in> \<^bold>~ A) \<^bold>\<rightarrow> (C \<^bold>\<notin> A \<^bold>\<and> C \<^bold>\<in> \<^bold>~ A)) \<^bold>\<and> ((B \<^bold>\<notin> A \<^bold>\<and> B \<^bold>\<notin> \<^bold>~ A) \<^bold>\<rightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<^bold>\<or> C \<^bold>\<in> A) \<^bold>\<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))) w" by(simp add: a1 MAX)
    hence "\<exists>C. \<forall>A. (((B \<^bold>\<in> A) \<^bold>\<rightarrow> (C \<^bold>\<in> A \<^bold>\<and> C \<^bold>\<notin> \<^bold>~ A)) \<^bold>\<and> ((B \<^bold>\<in> \<^bold>~ A) \<^bold>\<rightarrow> (C \<^bold>\<notin> A \<^bold>\<and> C \<^bold>\<in> \<^bold>~ A)) \<^bold>\<and> ((B \<^bold>\<notin> A \<^bold>\<and> B \<^bold>\<notin> \<^bold>~ A) \<^bold>\<rightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<^bold>\<or> C \<^bold>\<in> A) \<^bold>\<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))) w" by simp
    then obtain C where o1: "\<forall>A. (((B \<^bold>\<in> A) \<^bold>\<rightarrow> (C \<^bold>\<in> A \<^bold>\<and> C \<^bold>\<notin> \<^bold>~ A)) \<^bold>\<and> ((B \<^bold>\<in> \<^bold>~ A) \<^bold>\<rightarrow> (C \<^bold>\<notin> A \<^bold>\<and> C \<^bold>\<in> \<^bold>~ A)) \<^bold>\<and> ((B \<^bold>\<notin> A \<^bold>\<and> B \<^bold>\<notin> \<^bold>~ A) \<^bold>\<rightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<^bold>\<or> C \<^bold>\<in> A) \<^bold>\<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))) w" by blast
    from o1 have f2: "(P C) w" using CONJ4 POSS1 POSS2 notcontains_def by metis
    from o1 have "\<forall>Y. ((P (C \<^bold>+ Y)) \<^bold>\<rightarrow> C \<^bold>\<in> Y) w" using CONJ4 CONJ5 CONT2 NEG6 notcontains_def by (meson NEG5)
    hence "(\<^bold>\<Or>x. x \<^bold>\<in> B) w" using CONT1 indconcept_def indexists_def o1 f2 by auto
  }
  thus ?thesis by simp
  qed
have "\<lfloor>(\<^bold>\<Or>x. x \<^bold>\<in> B) \<^bold>\<rightarrow> (P B)\<rfloor>" using POSS1 indconcept_def indexists_def by auto
with f1 show "\<lfloor>(P B) \<^bold>\<leftrightarrow> (\<^bold>\<Or>x. x \<^bold>\<in> B)\<rfloor>" by blast
qed
(*As a side note: It follows from this that everything that is a non-contradictory 
concept sans (non-)existence predicate does in fact exist.
So this axiomatization implies flying elephants  *)
(*Also note that MAX is used in this proof*)

lemma CONT5': "\<lfloor>B \<^bold>\<in> C \<^bold>\<leftrightarrow> (\<^bold>\<And>X. (X \<^bold>\<in> B) \<^bold>\<rightarrow> X \<^bold>\<in> C)\<rfloor>"
proof -
have "\<lfloor>B \<^bold>\<in> C \<^bold>\<rightarrow> (\<^bold>\<And>X. (X \<^bold>\<in> B) \<^bold>\<rightarrow> X \<^bold>\<in> C)\<rfloor>" by (metis (no_types, lifting) CONT2 indforall_def)
moreover
have "\<lfloor>(\<^bold>\<And>X. (X \<^bold>\<in> B) \<^bold>\<rightarrow> X \<^bold>\<in> C) \<^bold>\<rightarrow> B \<^bold>\<in> C\<rfloor>"
  proof -
  {
    fix w :: i
    assume a1: "(\<^bold>\<And>X. (X \<^bold>\<in> B) \<^bold>\<rightarrow> X \<^bold>\<in> C) w"
      {
      assume a2: "(B \<^bold>\<notin> C) w"
      hence "\<exists>A. (B \<^bold>\<notin> A \<^bold>\<and> C \<^bold>\<in> A) w" using CONT1 by blast
      then obtain A where o1: "(B \<^bold>\<notin> A \<^bold>\<and> C \<^bold>\<in> A) w" by blast
      hence "(B \<^bold>\<notin> A) w" by simp
      hence "((B \<^bold>\<in> \<^bold>~ A) \<^bold>\<or> (B \<^bold>\<notin> A \<^bold>\<and> B \<^bold>\<notin> A)) w" by simp
      hence "\<exists>E. (E \<^bold>\<in> B \<^bold>\<and> (E \<^bold>\<in> \<^bold>~ A) \<^bold>\<and> (P E)) w" using CONJ4 CONJ5 POSS2 notcontains_def o1 by meson
      then obtain E where o2: "(E \<^bold>\<in> B \<^bold>\<and> (E \<^bold>\<in> \<^bold>~ A) \<^bold>\<and> (P E)) w" by blast
      hence "(P E) w" by simp
      hence "(\<^bold>\<exists>C. \<^bold>\<forall>A. ((E \<^bold>\<in> A) \<^bold>\<rightarrow> (C \<^bold>\<in> A \<^bold>\<and> C \<^bold>\<notin> \<^bold>~ A)) \<^bold>\<and> ((E \<^bold>\<in> \<^bold>~ A) \<^bold>\<rightarrow> (C \<^bold>\<notin> A \<^bold>\<and> C \<^bold>\<in> \<^bold>~ A)) \<^bold>\<and> ((E \<^bold>\<notin> A \<^bold>\<and> E \<^bold>\<notin> \<^bold>~ A) \<^bold>\<rightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<^bold>\<or> C \<^bold>\<in> A) \<^bold>\<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))) w" by(simp add: MAX)
      hence "\<exists>C. \<forall>A. (((E \<^bold>\<in> A) \<^bold>\<rightarrow> (C \<^bold>\<in> A \<^bold>\<and> C \<^bold>\<notin> \<^bold>~ A)) \<^bold>\<and> ((E \<^bold>\<in> \<^bold>~ A) \<^bold>\<rightarrow> (C \<^bold>\<notin> A \<^bold>\<and> C \<^bold>\<in> \<^bold>~ A)) \<^bold>\<and> ((E \<^bold>\<notin> A \<^bold>\<and> E \<^bold>\<notin> \<^bold>~ A) \<^bold>\<rightarrow> (((C \<^bold>\<in> \<^bold>~ A) \<^bold>\<or> C \<^bold>\<in> A) \<^bold>\<and> (C \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))) w" by simp
      then obtain D where o3: "\<forall>A. (((E \<^bold>\<in> A) \<^bold>\<rightarrow> (D \<^bold>\<in> A \<^bold>\<and> D \<^bold>\<notin> \<^bold>~ A)) \<^bold>\<and> ((E \<^bold>\<in> \<^bold>~ A) \<^bold>\<rightarrow> (D \<^bold>\<notin> A \<^bold>\<and> D \<^bold>\<in> \<^bold>~ A)) \<^bold>\<and> ((E \<^bold>\<notin> A \<^bold>\<and> E \<^bold>\<notin> \<^bold>~ A) \<^bold>\<rightarrow> (((D \<^bold>\<in> \<^bold>~ A) \<^bold>\<or> D \<^bold>\<in> A) \<^bold>\<and> (D \<^bold>\<notin> A \<^bold>+ \<^bold>~ A)))) w" by blast
      with o2 have "(D \<^bold>\<notin> A) w" by simp
      with o1 have "(D \<^bold>\<notin> C) w" using CONT2 notcontains_def by meson
      moreover
      from o3 have "(Ind D) w" by (metis (mono_tags, lifting) CONJ5 IND1 NEG6 NEG8 POSS1 notcontains_def)
      moreover
      from o2 o3 have "(D \<^bold>\<in> B) w" by simp
      ultimately
      have "(\<^bold>\<Or>X. \<^bold>\<not> ((X \<^bold>\<in> B) \<^bold>\<rightarrow> X \<^bold>\<in> C)) w" using indexists_def notcontains_def by auto
      hence "(\<^bold>\<not> (\<^bold>\<And>X. (X \<^bold>\<in> B) \<^bold>\<rightarrow> X \<^bold>\<in> C)) w" by (simp add: indexists_def indforall_def)
    }
    with a1 have "(B \<^bold>\<in> C) w" using notcontains_def by auto
  }
  thus ?thesis by simp
  qed
ultimately
show ?thesis by blast
qed
(*Note that MAX is used in this proof *)



lemma True nitpick[user_axioms, expect=genuine, satisfy] oops
(*Nitpick finds a model; however it is the "empty assignment". Not sure about nitpicks inner workings
to determine if that is a problem.*)


lemma MC: "\<lfloor>\<^bold>\<forall>x. (x \<^bold>\<rightarrow> \<^bold>\<box>x)\<rfloor>" nitpick[user_axioms] oops
(* No Modal Collapse *)
end