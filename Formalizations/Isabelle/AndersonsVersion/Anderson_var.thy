(*<*) 
theory Anderson_var
imports Main 

begin
(*>*)

section {* An Embedding of QML S5 in HOL *}

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

  consts eiw :: "\<mu> \<Rightarrow> i \<Rightarrow> bool"
  axiomatization where nonempty: "\<forall>w. \<exists>x. eiw x w"

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 51) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 50) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 49) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 48) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  abbreviation mforalli :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>i") where "\<forall>i \<Phi> \<equiv> (\<lambda>w. \<forall>x. (eiw x w) \<longrightarrow> (\<Phi> x w))"     
  abbreviation mexistsi :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>i") where "\<exists>i \<Phi> \<equiv> (\<lambda>w. \<exists>x. (eiw x w) \<and> \<Phi> x w)" 
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=" 52) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>. (\<phi> x m\<rightarrow> \<phi> y))"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

  axiomatization where 
  sym: "x r y \<longrightarrow> y r x" and
  refl: "x r x" and
  trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"


 
text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  

section {* Anderson's Ontological Argument -- varying domain*}  
text{* The formalisation follows Fitting's 'Types, Tableaus, and Gödels God' *}  
  
  consts Defective :: "\<mu> \<Rightarrow> \<sigma>" 

 --{*
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  *}
  
  definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
  "P = (\<lambda>\<Phi>. \<box> (\<forall>(\<lambda>x. (m\<not> (\<Phi>(x))) m\<rightarrow> Defective(x))))"
  
  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ( (\<box> (\<Phi> x )) m\<equiv> P \<Phi> ) ))" 
  
  
  definition fitting_ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "fitting_ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>i(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 

  definition anderson_ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "anderson_ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  (\<forall>i(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
 
   definition fuhrmann_ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "fuhrmann_ess = (\<lambda>\<Phi>. \<lambda>x. (\<Phi> x m\<and> ( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>i(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
    
  theorem fitting_implies_fuhrmann: "[\<forall>(\<lambda>\<Phi>. \<forall>i(\<lambda>x. fitting_ess \<Phi> x m\<rightarrow>  \<Phi> x)) ]"
  by (metis Anderson_var.refl fitting_ess_def)

  text {* The two box definition of essence is not equivalent to the original definition
        in Anderson's paper. *}
  theorem test: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>x. anderson_ess \<Phi> x m\<equiv> fitting_ess \<Phi> x)) ]"
  nitpick[user_axioms] oops
  
  
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. anderson_ess \<Phi> x m\<rightarrow> (\<box> (\<exists>i(\<lambda>y. \<Phi> y)))))"

  text{* Leon: Aligned A1 to the constant version. *}
  axiomatization where
    A1: "[\<forall>(\<lambda>\<Phi>. ( (P (\<lambda>x. m\<not> (\<Phi> x)))) m\<rightarrow> m\<not> (P \<Phi>))]" and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>i(\<lambda>x. (\<Phi> x) m\<rightarrow> (\<Psi> x) ))) m\<rightarrow> (P \<Psi>)))]" and
    A3:  "[P G]" 
 
  theorem T1: "[\<forall>(\<lambda>\<Phi>. (P \<Phi>) m\<rightarrow> \<diamond> (\<exists> \<Phi>))]"
  by (metis A1 A2)
        
  corollary C1: "[\<diamond> (\<exists> G)]"
  by (metis A3 T1)
  
  lemma T2_lem: "[\<forall>i(\<lambda>x. \<forall>(\<lambda>\<Phi>. ((G x) m\<and> (anderson_ess \<Phi> x)) m\<rightarrow> \<forall>i(\<lambda>y. ((G y) m\<rightarrow> \<Phi> y))))]"
  by (metis Anderson_var.refl G_def anderson_ess_def)
  
  -- {* Satallax provides a proof but metis fails to reconstruct it.*}
  theorem T2: "[\<forall>i(\<lambda>x. (G x) m\<rightarrow> (anderson_ess G x))]"
 --{*by (metis A2 A3 A4 Anderson_var.refl G_def anderson_ess_def nonempty)*}
  oops

  --{*
  axiomatization where
  T2: "[\<forall>i(\<lambda>x. (G x) m\<rightarrow> (ess G x))]"
  *}
 

theorem T3: "[\<box> (\<exists>(\<lambda>x. (G x)))]"
 by (metis  A3 G_def sym T1)

   
  corollary C2: "[\<exists>(\<lambda>x. (G x) )]"
  by (metis Anderson_var.sym C1 T3)


text {* The consistency of the entire theory is confirmed by Nitpick. *}
   lemma True 
   nitpick [satisfy, user_axioms, expect = genuine] oops


section {* Modal Collapse *}  
 
  --{* Nitpick generates counter model but the cardinality of the set of individuals
    is lower (1) than the one used by Anderson (2). 
    
    Leon: Without introducing T2, A4, A5 the cardinalities of the counter model match those of Anderson and 
    our formalized constant domain variant.
    *}
  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms]
  oops

  theorem  A4:  "[\<forall>(\<lambda>\<Phi>. (P \<Phi>) m\<rightarrow> \<box> (P \<Phi>))]"

  by (metis A3 Anderson_var.trans C2 G_def)
 
  
  --{* Leon: Leo-2 gives up on this and I have troubles calling satallax 
      (it seems to surrender instantly disregarding of which problem it is called on
      Nitpick fails to find a counter model, though.
      *}
theorem A5:  "[P NE]"
  --{*nitpick[user_axioms]*}
  oops
 
(*<*) 
end
(*>*) 
