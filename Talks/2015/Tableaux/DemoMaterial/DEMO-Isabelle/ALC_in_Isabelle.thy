theory ALC_in_Isabelle imports Main begin
typedecl i  type_synonym \<tau> = "(i \<Rightarrow> bool)" type_synonym \<sigma> = "(i \<Rightarrow> i \<Rightarrow> bool)"

(* ALC: Syntax und Semantik *)
abbreviation bot         ("\<bottom>")             where "\<bottom>     \<equiv> \<lambda>x. False"
abbreviation top         ("\<top>")             where "\<top>     \<equiv> \<lambda>x. True"
abbreviation neg         ("\<sim>")             where "\<sim>A    \<equiv> \<lambda>x. \<not>A(x)"
abbreviation disj        (infixr "\<squnion>" 40)   where "A \<squnion> B  \<equiv> \<lambda>x. A(x) \<or> B(x)"
abbreviation conj        (infixr "\<sqinter>" 41)   where "A \<sqinter> B  \<equiv> \<lambda>x. A(x) \<and> B(x)"
abbreviation exi_r       ("\<exists>")             where "\<exists>r A   \<equiv> \<lambda>x. \<exists>y. r x y \<and> A(y)"
abbreviation all_r       ("\<forall>")             where "\<forall>r A   \<equiv> \<lambda>x. \<forall>y. r x y \<longrightarrow> A(y)"

abbreviation sub   (infixr "\<sqsubseteq>" 39)         where "A \<sqsubseteq> B \<equiv> \<forall>x. A(x) \<longrightarrow> B(x)"
abbreviation eq    (infixr "\<doteq>" 38)         where "A \<doteq> B \<equiv> A \<sqsubseteq> B \<and> B \<sqsubseteq> A"

(* ALC: Einfache Meta-Theorie; Lemmata aus Vortrag *)
lemma L1: "\<top> \<doteq> A \<squnion> \<sim>A"                  by metis
lemma L2: "\<bottom> \<doteq> \<sim>\<top>"                      by metis 
lemma L3: "A \<sqinter> B \<doteq> \<sim>(\<sim>A \<squnion> \<sim>B)"          by metis
lemma L4: "\<exists>r C \<doteq> \<sim>(\<forall>r (\<sim>C))"            by metis
lemma L5: "(A \<sqsubseteq> B) \<equiv> \<exists>X.(A \<doteq> (X \<sqinter> B))"   sledgehammer [remote_leo2] oops
lemma L6: "(A \<sqsubseteq> B) \<equiv> ((A \<sqinter> \<sim>B) \<doteq> \<bottom>)"    sledgehammer [remote_leo2] oops

(* ALC: Beispiel Signatur *)
consts HappyMan::"\<tau>" Human::"\<tau>" Female::"\<tau>" Doctor::"\<tau>" Professor::"\<tau>"    (* Konzepte *)
consts married::"\<sigma>" hasChild::"\<sigma>"                                        (* Rollen *)
consts BOB::"i" MARY::"i"                                                (* Individuen *)
axiomatization where diff1: "BOB \<noteq> MARY"

(* ALC: Beispiel für TBox *)
axiomatization where
  tbox1: "HappyMan \<doteq> (Human\<sqinter>\<sim>Female\<sqinter>(\<exists>married Doctor)\<sqinter>(\<forall>hasChild (Doctor\<squnion>Professor)))" and
  tbox2: "Doctor \<sqsubseteq> Human" and
  tbox3: "Professor \<sqsubseteq> Human"

(* Einfache Anfragen *)
lemma "HappyMan \<sqsubseteq> \<exists>married Human" nitpick [user_axioms] oops        (* no countermodel found *)
lemma "HappyMan \<sqsubseteq> \<exists>married Human" sledgehammer [remote_leo2] oops          

(* Beispiel für ABox *)
axiomatization where 
  abox1: "HappyMan BOB" and 
  abox2: "hasChild BOB MARY" and
  abox3: "\<not> Doctor MARY" 

(* KB=(TBox,ABox) Konsistenz *)
lemma "HappyMan a" nitpick [satisfy,user_axioms,expect = genuine] oops

(* Soundness der ALC-Tableauxregeln *)
lemma "(A \<sqinter> B)(x) \<longrightarrow> (A(x) \<and> B(x))"         by auto
lemma "(A \<squnion> B)(x) \<longrightarrow> (A(x) \<or> B(x))"         by auto 
lemma "(\<exists>r A)(x)  \<longrightarrow>  (\<exists>b. (r x b \<and> A b))"  by auto
lemma "((\<forall>r A)(x) \<and> r x y)   \<longrightarrow>  A y"       by auto
lemma "(A(x) \<and> \<sim>A(x)) \<longrightarrow> False"             by auto

(* Korrespondenz ALC zu Modallogik *)
   (* ist ebenso einfach *)
 
end
