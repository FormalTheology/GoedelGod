(*<*) 
theory Bjordal_B_var
imports Main "../QML_var"

begin
(*>*)

section {* Introduction *}

text {* We verify Frode Bjordal's paper from 1998. 
In this file Bjordal_B.thy we address the claim that
Gödel's axioms A2, A3 and A4, and
also Gödel's Definition D1 imply alternative definition D 
(where God is taken as a primitive symbol) implies  *}
  
section {* Bjordal's argument *}  
 
text {* Constant symbol @{text "P"} (for 'Positive') is introduced
here as a primitive constant. Then G is defined using P. This is
Gödel's definition D1. *}  

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  definition G :: "\<mu> \<Rightarrow> \<sigma>"  where "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<Phi> x))" 

text {* We postulate Gödel's axioms A2, A3 and A4. *}

 axiomatization where
  A2: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" and     
  A3: "[P G]" and
  A4: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]"


text {* We then show, using two lemmas, that Bjordal's definition 
D is implied. *}

 lemma Case1: "[\<forall>(\<lambda>\<Phi>. (\<box>(\<forall>e(\<lambda>x. G x m\<rightarrow> \<Phi> x))) m\<rightarrow> P \<Phi>)]"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis A2 A3) 

 lemma Case2: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> (\<box>(\<forall>e(\<lambda>x. G x m\<rightarrow> \<Phi> x))))]"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis A4 G_def) 

 theorem D1: "P = (\<lambda>\<Phi>. \<box>(\<forall>e(\<lambda>x. G x m\<rightarrow> \<Phi> x)))"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis Case1 Case2) 

(*<*) 
end
(*>*) 