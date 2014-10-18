(*<*) 
theory Bjordal_A
imports Main

begin
(*>*)

section {* Introduction *}

text {* We verify Frode Bjordal's paper from 1998. 
In this file Bjordal_A.thy we address the claim that
Bjordal's alternative definition D (where God is taken as 
a primitive symbol) implies Gödel's axioms A2, A3 and A4, and
also Gödel's Definition D1. *}

section {* An Embedding of QML KB in HOL *}

text {* The types @{text "i"} for possible worlds and $\mu$ for individuals are introduced. *}

  typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for indiviuals"      

text {* Possible worlds are connected by an accessibility relation @{text "r"}.*} 

  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"   

text {* QML formulas are translated as HOL terms of type @{typ "i \<Rightarrow> bool"}. 
This type is abbreviated as @{text "\<sigma>"}. *}

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"
 
text {* The classical connectives $\neg, \wedge, \rightarrow$, and $\forall$
(over individuals and over sets of individuals) and $\exists$ (over individuals) are
lifted to type $\sigma$. The lifted connectives are @{text "m\<not>"}, @{text "m\<and>"}, @{text "m\<rightarrow>"},
@{text "\<forall>"}, and @{text "\<exists>"} (the latter two are modeled as constant symbols). 
Other connectives can be introduced analogously. We exemplarily do this for @{text "m\<or>"} , 
@{text "m\<equiv>"}, and @{text "mL="} (Leibniz equality on individuals). Moreover, the modal 
operators @{text "\<box>"} and @{text "\<diamond>"}  are introduced. Definitions could be used instead of 
abbreviations. *}

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 51) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 50) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 49) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 48) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=" 52) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>. (\<phi> x m\<rightarrow> \<phi> y))"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 
  
text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  

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