(*<*) 
theory ModalCollapse
imports Main 

begin
(*>*)

section {* An Embedding of QML S5 in HOL *}

text {* The types @{text "i"} for possible worlds and $\mu$ for individuals are introduced. *}

  typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for individuals"      

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
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

text {* Possibilist quantifiers *}

  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"

text {* Actualist e-quantifiers *}

  consts eiw :: "\<mu> \<Rightarrow> i \<Rightarrow> bool"
  (* axiomatization where nonempty: "\<forall>w. \<exists>x. eiw x w" *)
  abbreviation mforalle :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>e") where "\<forall>e \<Phi> \<equiv> (\<lambda>w. \<forall>x. (eiw x w) \<longrightarrow> (\<Phi> x w))"     
  abbreviation mexistse :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>e") where "\<exists>e \<Phi> \<equiv> (\<lambda>w. \<exists>x. (eiw x w) \<and> \<Phi> x w)" 

text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"

text {* Abbreviations for various conditions that can be imposed on the accessibility relation  *}

  abbreviation sym :: "bool" ("sym") where  "sym \<equiv> \<forall>x.\<forall>y.(x r y \<longrightarrow> y r x)"
  abbreviation refl :: "bool" ("refl") where "refl \<equiv> \<forall>x. (x r x)"
  abbreviation trans :: "bool" ("trans") where "trans \<equiv> \<forall>x.\<forall>y.\<forall>z. ((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"


section {* Modal Collapse *}  

text {* Three kinds of Modal Collapse *}

  abbreviation f_collapse_contingent_to_necessary :: "\<sigma> \<Rightarrow> \<sigma>" ("cCN")
         where "cCN \<Phi> \<equiv> \<Phi> m\<rightarrow> (\<box> \<Phi>)"

  abbreviation f_collapse_possible_to_necessary :: "\<sigma> \<Rightarrow> \<sigma>" ("cPN") 
         where "cPN \<Phi> \<equiv> (\<diamond> \<Phi>) m\<rightarrow> (\<box> \<Phi>)" 

  abbreviation f_collapse :: "\<sigma> \<Rightarrow> \<sigma>" ("c") 
         where "c \<Phi> \<equiv> (\<Phi> m\<equiv> (\<box> \<Phi>)) m\<and> ((\<box> \<Phi>) m\<equiv> (\<diamond> \<Phi>)) "

  abbreviation collapseCN  :: "\<sigma>" ("collapseCN") where "collapseCN \<equiv> \<forall>(\<lambda>\<Phi>. (cCN \<Phi>))"
  abbreviation collapsePN :: "\<sigma>" ("collapsePN") where "collapsePN \<equiv> \<forall>(\<lambda>\<Phi>. (cPN \<Phi>))"
  abbreviation collapse :: "\<sigma>" ("collapse") where "collapse \<equiv> \<forall>(\<lambda>\<Phi>. (c \<Phi>))"


  (* apparently Leo2 and Satallax succeed, but metis fails. *)
  theorem collapseCN_implies_collapsePN : "[collapseCN m\<rightarrow> collapsePN]"
  sledgehammer [provers = remote_satallax remote_leo2, timeout = 30, strict]
  (* by metis *)
  oops

  (* apparently, Leo2 and Satallax succeed, but metis fails. *)
  theorem collapseCN_entails_collapsePN : "[collapseCN] \<longrightarrow> [collapsePN]"
  sledgehammer [provers = remote_satallax remote_leo2, timeout = 30, strict]
  (* by metis *)
  oops

  theorem test1 : "[\<forall>(\<lambda>\<psi>. \<forall>(\<lambda>\<Phi>. (\<Phi> m\<rightarrow> \<psi>)) m\<rightarrow> \<forall>(\<lambda>\<Phi>. ((\<diamond> \<Phi>) m\<rightarrow> \<psi>)))]"
  sledgehammer [provers = remote_satallax remote_leo2, timeout = 30, strict]
  oops

  theorem test2 : "[\<forall>(\<lambda>\<psi>. \<forall>(\<lambda>\<Phi>. (\<Phi> m\<rightarrow> \<psi>)))] \<longrightarrow> [\<forall>(\<lambda>\<psi>. \<forall>(\<lambda>\<Phi>. ((\<diamond> \<Phi>) m\<rightarrow> \<psi>)))]"
  sledgehammer [provers = remote_satallax remote_leo2, timeout = 30, strict]
  nitpick
  oops

  (* with the help of symmetry, metis succeeds *)
  theorem with_sym_collapseCN_entails_collapsePN : 
          "sym \<longrightarrow> ([collapseCN] \<longrightarrow> [collapsePN])"
  by metis
 

text {* As shown by nitpick, in Modal Logic K, 
        collapseCN does not entail collapse *}

  theorem collapseCN_entails_collapse : 
          "[collapseCN] \<longrightarrow> [collapse]"
  nitpick oops


text {* Hence, trivially, collapseCN also does not imply collapse *}
  
  theorem collapseCN_implies_collapse : 
          "[collapseCN m\<rightarrow> collapse]"
  nitpick oops




text {* It suffices to require reflexivity of the accesibility relation, 
        to ensure that collapseCN entails collapse *}

  (* apparently Leo2 and Satallax succeed, but metis fails. *)
  theorem with_refl_collapseCN_entails_collapse : 
          "refl \<longrightarrow>  ([collapseCN] \<longrightarrow> [collapse])"
  sledgehammer [provers = remote_leo2 remote_satallax, verbose]
  (* by metis *)
  oops
  
  (* again, with the help of symmetry, metis succeeds *)
  theorem with_sym_refl_collapseCN_entails_collapse : 
          "(sym \<and> refl) \<longrightarrow> ([collapseCN] \<longrightarrow> [collapse])"
  by metis


text {* Moreover, with reflexivity, 
        collapseCN not only entails but also implies collapse *}

  (* Satallax succeeds, but now Leo2 times out. And Metis still fails. *)
  theorem with_refl_collapseCN_implies_collapse : 
          "refl \<longrightarrow>  ([collapseCN m\<rightarrow> collapse])"
  sledgehammer [provers = remote_leo2 remote_satallax, verbose, timeout = 30]
  (* by metis *)
  oops

  (* now even with the help of symmetry Metis fails. Leo2 still times out. Satallax succeeds. *)
  theorem with_sym_refl_collapseCN_implies_collapse : 
          "(sym \<and> refl) \<longrightarrow> ([collapseCN m\<rightarrow> collapse])"
  sledgehammer [provers = remote_leo2 remote_satallax]
  (* by metis *)
  oops

section {* Partial Modal Collapse on Restricted Sets of Propositions *}

text {* An interesting question: 
        is the set of properties for which the collapse holds closed under implication?
        The following counter models and theorems partially answer this question.  *}

  theorem MC1: "\<forall>\<Phi>.\<forall>\<Psi>. [cCN \<Phi>] \<longrightarrow> [\<Psi> m\<rightarrow> \<Phi>] \<longrightarrow> [cCN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC2: "\<forall>\<Phi>.\<forall>\<Psi>. [cCN \<Phi>] \<longrightarrow> [\<Phi> m\<rightarrow> \<Psi>] \<longrightarrow> [cCN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC3: "\<forall>\<Phi>.\<forall>\<Psi>. [cCN \<Phi>] \<longrightarrow> [\<box> \<Phi> m\<rightarrow> \<box> \<Psi>] \<longrightarrow> [cCN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC4: "\<forall>\<Phi>.\<forall>\<Psi>. [cCN \<Phi>] \<longrightarrow> [\<Phi> m\<equiv> \<Psi>] \<longrightarrow> [cCN \<Psi>]"
  by metis

  theorem MC5: "\<forall>\<Phi>.\<forall>\<Psi>. [cPN \<Phi>] \<longrightarrow> [\<Phi> m\<rightarrow> \<Psi>] \<longrightarrow> [cPN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC6: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> [\<Psi> m\<rightarrow> \<Phi>] \<longrightarrow> [cCN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC7: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> [\<Phi> m\<rightarrow> \<Psi>] \<longrightarrow> [cCN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC8: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> ([\<Phi>] \<longrightarrow> [\<Psi>]) \<longrightarrow> [cCN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC9: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> ([\<Phi>] \<longleftrightarrow> [\<Psi>]) \<longrightarrow> [cCN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC10: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> [\<Phi> m\<rightarrow> (\<box> \<Psi>)] \<longrightarrow> [cCN \<Psi>]"
  nitpick [user_axioms]
  oops

  theorem MC11: "\<exists>R. \<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> [(R \<Phi> \<Psi>)] \<longrightarrow> [cCN \<Psi>]"
  (* sledgehammer [provers = remote_satallax remote_leo2] *)
  oops

  theorem MC12: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> [\<Phi>] \<longrightarrow> [\<Phi> m\<rightarrow> \<Psi>] \<longrightarrow> [cCN \<Psi>]"
  by metis

  theorem MC13: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl) \<longrightarrow> [\<Phi>] \<longrightarrow> [\<Phi> m\<rightarrow> \<Psi>] \<longrightarrow> [cCN \<Psi>]"
  by metis

  theorem MC14: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl) \<longrightarrow> [\<Phi> m\<rightarrow> ((\<Phi> m\<rightarrow> \<Psi>) m\<rightarrow> (cCN \<Psi>))]"
  nitpick
  oops

  theorem MC15: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> [cCN (\<Phi> m\<rightarrow> \<Psi>)] \<longrightarrow> [cCN \<Psi>]"
  nitpick
  oops

  theorem MC16: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>] \<and> [cCN \<Psi>]) \<longrightarrow> [cCN (\<Phi> m\<and> \<Psi>)]"
  by metis

  theorem MC17: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>] \<and> [cCN (\<Phi> m\<rightarrow> \<Psi>)]) \<longrightarrow> [cCN \<Psi>]"
  nitpick
  oops

  theorem MC18: "\<forall>\<Phi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> [cCN (cCN \<Phi>)]"
  by metis

  theorem MC19: "\<forall>\<Phi>. [cCN \<Phi>] \<longrightarrow> [cCN (cCN \<Phi>)]"
  by metis

  theorem MC20: "\<forall>\<Phi>. [(cCN \<Phi>) m\<rightarrow> (cCN (cCN \<Phi>))]"
  nitpick
  oops

  theorem MC21: "\<forall>\<Phi>. [\<Phi>] \<longrightarrow> [cCN \<Phi>]"
  by metis

  theorem MC22: "\<forall>\<Phi>. [cCN (cCN \<Phi>)] \<longrightarrow> [cCN \<Phi>]"
  nitpick
  oops

  theorem MC23: "\<forall>\<Phi>.\<forall>\<Psi>. (sym \<and> trans \<and> refl \<and> [cCN \<Phi>]) \<longrightarrow> [cCN (\<Phi> m\<or> \<Psi>)]"
  nitpick
  oops
 



section {* Miscellanea *} 

  consts G :: "\<mu> \<Rightarrow> \<sigma>"

  abbreviation L1 :: "\<sigma>" ("L1") where "L1 \<equiv> (cCN (\<exists>(\<lambda>x.(G x))))"
  abbreviation L2 :: "\<sigma>" ("L2") where "L2 \<equiv> (cPN (\<exists>(\<lambda>x.(G x))))"  


(*<*) 
end
(*>*) 
