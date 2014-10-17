(*<*) 
theory Bjordal_A_constant_domain
imports Main QML_K_constant_domain

begin
(*>*)

section {* Introduction *}

text {* We verify Frode Bjordal's paper from 1998. 
In this file Bjordal_A.thy we address the claim that
Bjordal's alternative definition D (where God is taken as 
a primitive symbol) implies Gödel's axioms A2, A3 and A4, and
also Gödel's Definition D1. *}

section {* Bjordal's argument *}  
  
text {* Constant symbol @{text "G"} (for 'God') is introduced
here as a primitive constant. Then P is defined using G. This
is Bjordal's definition D. *}

 consts G :: "\<mu> \<Rightarrow> \<sigma>"   
 definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  where "P = (\<lambda>\<Phi>. \<box>(\<forall>(\<lambda>x. G x m\<rightarrow> \<Phi> x)))" 

text {* Gödel's axioms A2, A3 and A4, and even his definition D1 
can actually be derived from this alternative definition. *}

 theorem A2: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" 
 (* sledgehammer [provers = remote_leo2] *)
 by (simp add: P_def) 

 theorem A3: "[P G]"
 (* sledgehammer [provers = remote_leo2] *)
 by (metis P_def)

text {* For proving A4 we need transitivity. *}

 axiomatization where 
  trans: "x r y \<and> y r z \<longrightarrow> x r z"
 
 theorem A4: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis trans P_def)

text {* For proving D1 we need reflexivity . *}

 axiomatization where 
  refl: "x r x" 

 theorem D1: "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<Phi> x))"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis refl P_def)



  abbreviation f_collapse_contingent_to_necessary :: "\<sigma> \<Rightarrow> \<sigma>" ("cCN")
         where "cCN \<Phi> \<equiv> \<Phi> m\<rightarrow> (\<box> \<Phi>)"

  abbreviation f_collapse_possible_to_necessary :: "\<sigma> \<Rightarrow> \<sigma>" ("cPN") 
         where "cPN \<Phi> \<equiv> (\<diamond> \<Phi>) m\<rightarrow> (\<box> \<Phi>)" 

  abbreviation f_collapse :: "\<sigma> \<Rightarrow> \<sigma>" ("c") 
         where "c \<Phi> \<equiv> (\<Phi> m\<equiv> (\<box> \<Phi>)) m\<and> ((\<box> \<Phi>) m\<equiv> (\<diamond> \<Phi>)) "

  abbreviation collapseCN  :: "\<sigma>" ("collapseCN") where "collapseCN \<equiv> \<forall>(\<lambda>\<Phi>. (cCN \<Phi>))"
  abbreviation collapsePN :: "\<sigma>" ("collapsePN") where "collapsePN \<equiv> \<forall>(\<lambda>\<Phi>. (cPN \<Phi>))"
  abbreviation collapse :: "\<sigma>" ("collapse") where "collapse \<equiv> \<forall>(\<lambda>\<Phi>. (c \<Phi>))"

  lemma MC1: "[\<forall>(\<lambda>\<phi>.\<forall>(\<lambda>x.(((P \<phi>) m\<and> (G x) ) m\<rightarrow> ((\<phi> x) m\<rightarrow> (\<box> (\<phi> x))))))]"
  nitpick [user_axioms]
  oops
 
  lemma MC2: "[\<forall>(\<lambda>\<phi>.\<forall>(\<lambda>x.((G x) m\<rightarrow> ((\<phi> x) m\<rightarrow> (\<box> (\<phi> x))))))]"
  nitpick [user_axioms]
  oops

  lemma MC3: "[\<forall>(\<lambda>\<phi>.\<forall>(\<lambda>x.((P \<phi>) m\<rightarrow> ((\<phi> x) m\<rightarrow> (\<box> (\<phi> x))))))]"
  nitpick [user_axioms]
  oops


(*<*) 
end
(*>*) 