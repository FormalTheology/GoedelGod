theory ALC  imports Main begin
typedecl i  type_synonym \<tau> = "(i \<Rightarrow> bool)" type_synonym \<sigma> = "(i \<Rightarrow> i \<Rightarrow> bool)"

(* ALC: Syntax und Semantic *)
abbreviation empty_concept                ("\<bottom>") where "\<bottom>    \<equiv> \<lambda>x. False"
abbreviation universal_concept            ("\<top>") where "\<top>    \<equiv> \<lambda>x. True"
abbreviation negation                     ("\<sim>") where "\<sim>A   \<equiv> \<lambda>x. \<not>A(x)"
abbreviation disjunction        (infixr "\<squnion>" 40) where "A \<squnion> B  \<equiv> \<lambda>x. A(x) \<or> B(x)"
abbreviation conjunction        (infixr "\<sqinter>" 41) where "A \<sqinter> B  \<equiv> \<lambda>x. A(x) \<and> B(x)"
abbreviation existential_role_restriction ("\<exists>") where "\<exists>r A  \<equiv> \<lambda>x. \<exists>y. r x y \<and> A(y)"
abbreviation universal_role_restriction   ("\<forall>") where "\<forall>r A  \<equiv> \<lambda>x. \<forall>y. r x y \<longrightarrow> A(y)"

abbreviation subsumtion        (infixr "\<sqsubseteq>" 39) where "A\<sqsubseteq>B  \<equiv> \<forall>x. A(x) \<longrightarrow> B(x)"
abbreviation equality          (infixr "\<doteq>" 38) where "A \<doteq> B \<equiv> A \<sqsubseteq> B \<and> B \<sqsubseteq> A"

(* ALC: Simple Meta-Theory Examples *)
lemma L1: "\<top> \<doteq> \<sim>\<bottom>"                      by metis 
lemma L2: "A\<sqinter>B \<doteq> \<sim>(\<sim>A\<squnion>\<sim>B)"              by metis
lemma L3: "\<exists>r C \<doteq> \<sim>(\<forall>r (\<sim>C))"            by metis
lemma L4: "(A \<sqsubseteq> B) \<equiv> \<exists>X.(A \<doteq> (X \<sqinter> B))"   sledgehammer [remote_leo2] oops
lemma L5: "(A \<sqsubseteq> B) \<equiv> ((A \<sqinter> \<sim>B) \<doteq> \<bottom>)"    sledgehammer [remote_leo2] oops

(* ALC: Example Signatur *)
consts HappyMan::"\<tau>" Human::"\<tau>" Female::"\<tau>" Doctor::"\<tau>" Professor::"\<tau>"  (* Concepts *)
consts married::"\<sigma>" hasChild::"\<sigma>"                                      (* Roles *)
consts BOB::"i" MARY::"i"                                              (* Individuals *)
axiomatization where diff1: "BOB \<noteq> MARY"

(* ALC: Simple TBox Example *)
axiomatization where
  tbox1: "HappyMan \<doteq> (Human\<sqinter>\<sim>Female\<sqinter>(\<exists>married Doctor)\<sqinter>(\<forall>hasChild (Doctor\<squnion>Professor)))" and
  tbox2: "Doctor \<sqsubseteq> Human" and
  tbox3: "Professor \<sqsubseteq> Human"

(* ALC: Example Queries *)
lemma "HappyMan \<sqsubseteq> \<exists>married Human" nitpick [user_axioms] oops (* no countermodel found *)
lemma "HappyMan \<sqsubseteq> \<exists>married Human" by (metis tbox1 tbox2) (* proof found *)
lemma "\<exists>married Human \<sqsubseteq> HappyMan" nitpick [user_axioms] oops

(* ALC: Simple ABox Example *)
axiomatization where 
  abox1: "HappyMan BOB" and 
  abox2: "hasChild BOB MARY" and
  abox3: "\<not> Doctor MARY" 

(* ALC: Example Query *)
lemma "(\<exists>married Human)(BOB)" by (metis abox1 tbox1 tbox2)

(* ALC: Consistency Check for KB=(TBox,ABox)  *)
lemma "HappyMan a" nitpick [satisfy,user_axioms,expect = genuine] oops

(* ALC: Soundness of ALC-Tableaurules *)
lemma "(A \<sqinter> B)(x) \<longrightarrow> (A(x) \<and> B(x))"        by metis
lemma "(A \<squnion> B)(x) \<longrightarrow> (A(x) \<or> B(x))"         by metis 
lemma "(\<exists>r A)(x)  \<longrightarrow>  (\<exists>b. (r x b \<and> A b))"  by metis
lemma "((\<forall>r A)(x) \<and> r x y)   \<longrightarrow>  A y"       by (metis (hide_lams, mono_tags))
lemma "(A(x) \<and> \<sim>A(x)) \<longrightarrow> False"            by metis

(* ALC: Correspondence with Modal Logic *)
 
abbreviation mfalse  ("m\<bottom>")           where "m\<bottom> \<equiv> \<lambda>w. False"    
abbreviation mtrue   ("m\<top>")           where "m\<top> \<equiv> \<lambda>w. True"    
abbreviation mnot    ("m\<not>")           where "m\<not> \<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)"    
abbreviation mand    (infixr "m\<and>" 51) where "\<phi> m\<and> \<psi> \<equiv> \<lambda>w. \<phi>(w) \<and> \<psi>(w)"   
abbreviation mor     (infixr "m\<or>" 50) where "\<phi> m\<or> \<psi> \<equiv> \<lambda>w. \<phi>(w) \<or> \<psi>(w)"   
abbreviation mbox    ("\<box>")            where "\<box>r \<phi> \<equiv> \<lambda>w. \<forall>v.  r w v \<longrightarrow> \<phi>(v)"
abbreviation mdia    ("\<diamond>")            where "\<diamond>r \<phi> \<equiv> \<lambda>w. \<exists>v. r w v \<and> \<phi>(v)" 

no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") 
abbreviation valid :: "\<tau> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"

lemma "\<top> = m\<top>"              by metis 
lemma "\<bottom> = m\<bottom>"              by metis 
lemma "(A \<sqinter> B) = (A m\<and> B)"  by metis 
lemma "(A \<squnion> B) = (A m\<or> B)"  by metis 
lemma "(\<forall>r A) = (\<box>r A)"     by metis
lemma "(\<exists>r A) = (\<diamond>r A)"      by metis
end
