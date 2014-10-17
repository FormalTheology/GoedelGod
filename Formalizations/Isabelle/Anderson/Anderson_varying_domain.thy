(*<*) 
theory Anderson_varying_domain
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

  consts eiw :: "\<mu> \<Rightarrow> i \<Rightarrow> bool"
  axiomatization where nonempty: "\<forall>w. \<exists>x. eiw x w"

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 51) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 50) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 49) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 48) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  abbreviation mforalle :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>e") where "\<forall>e \<Phi> \<equiv> (\<lambda>w. \<forall>x. (eiw x w) \<longrightarrow> (\<Phi> x w))"     
  abbreviation mexistse :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>e") where "\<exists>e \<Phi> \<equiv> (\<lambda>w. \<exists>x. (eiw x w) \<and> \<Phi> x w)" 
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=" 52) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>. (\<phi> x m\<rightarrow> \<phi> y))"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"


section {* Anderson's Ontological Argument -- varying domain (individuals) *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<equiv>  ( (\<box> (\<Phi> x ))) ))" 

  axiomatization where
    A1:  "[\<forall>(\<lambda>\<Phi>. ((P \<Phi>) m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))) )  )]"  and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" and
    A3:  "[P G]" 

subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of C1 and T3 *}
  
  corollary C1: "[\<diamond> (\<exists>e G)]"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3)

  text {* we only need axiom B here *}
  axiomatization where sym: "x r y \<longrightarrow> y r x"
    
  theorem T3: "[\<box> (\<exists>e G)]"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3 sym G_def)

subsection {* Consistency again (now with sym) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of A4 and A5 *}

  text {* As noted by Petr Hajek, A4 and A5 can be derived
          from the other axioms and definitions. *}
  
  text {* for A4 we need transitivity *}
  axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

  theorem A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A3 G_def sym trans T3)

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>e(\<lambda>y. \<Phi> y)))))"

  theorem A5: "[P NE]"
  by (metis A2 A3 ess_def NE_def)

  text{* Fuhrmann remarks that these derivations depend on 
       "meist stillschweigen gemachten Annahmen über die 
       Logik der zweiten Stufe, die Anderson jedoch nicht teilt." *}


subsection {* Consistency again (now with sym and trans) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms]
  oops



(*<*) 
end
(*>*) 
