(*<*) 
theory Anderson_var
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

  axiomatization where 
  sym: "x r y \<longrightarrow> y r x" and
  refl: "x r x" and
  trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  

section {* Anderson's Ontological Argument -- varying domain*}   
  
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  
  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ( (\<box> (\<Phi> x )) m\<equiv> P \<Phi> ) ))" 
   
  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
  
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>e(\<lambda>y. \<Phi> y)))))"

  axiomatization where
    A1:  "[\<forall>(\<lambda>\<Phi>. ((P \<Phi>) m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))) )  )]" and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. (\<Phi> x) m\<rightarrow> (\<Psi> x) ))) m\<rightarrow> (P \<Psi>)))]" and
    A3:  "[P G]" 
 
  theorem T1: "[\<forall>(\<lambda>\<Phi>. (P \<Phi>) m\<rightarrow> \<diamond> (\<exists> \<Phi>))]"
  by (metis A1 A2)
        
  corollary C1: "[\<diamond> (\<exists> G)]"
  by (metis A3 T1)
  
  lemma T2_lem: "[\<forall>e(\<lambda>x. \<forall>(\<lambda>\<Phi>. ((G x) m\<and> (ess \<Phi> x)) m\<rightarrow> \<forall>e(\<lambda>y. ((G y) m\<rightarrow> \<Phi> y))))]"
  by (metis refl G_def ess_def)
  
  text {* For theorem T2, Satallax succeeds, but metis fails.*}
  theorem T2: "[\<forall>e(\<lambda>x. (G x) m\<rightarrow> (ess G x))]"
  -- {* sledgehammer min [provers = remote_satallax metis] (A2 A3 refl sym trans C1 G_def NE_def P_def T1 T2_lem anderson_ess_def nonempty) *}
  --{*by (metis A2 A3 refl sym trans C1 G_def NE_def P_def T1 T2_lem anderson_ess_def nonempty)*}
  oops
 
  theorem T3: "[\<box> (\<exists>(\<lambda>x. (G x)))]"
  by (metis A3 G_def sym T1)
   
  --{* It is surprising that Metis finds a proof using "sym". 
       Typically, the proof of C2 uses "refl" instead. *}
  corollary C2: "[\<exists>(\<lambda>x. (G x) )]"
  -- {* by (metis refl T3) *} 
  by (metis sym C1 T3)


text {* The consistency of the entire theory is confirmed by Nitpick. *}
   lemma True 
   nitpick [satisfy, user_axioms, expect = genuine] oops


section {* Provability of A4 and A5 *}

  theorem  A4:  "[\<forall>(\<lambda>\<Phi>. (P \<Phi>) m\<rightarrow> \<box> (P \<Phi>))]"
  --{* sledgehammer min [metis] (A3 trans C2 G_def) *}
  by (metis A3 trans sym T3 G_def)
 

  theorem A5:  "[P NE]"
  by (metis A2 A3 ess_def NE_def)


section {* Immunity to Modal Collapse *}  
 
  text {* Nitpick generates counter-model with 1 individual and 2 worlds, which is simpler than
          the counter-model with 2 individuals and 2 worlds presented by Anderson (1990, in page 7). 
       *}

  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms]
  oops




section {* Fuhrmann's Alternative Definition of Essence *}

  definition fuhrmann_ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "fuhrmann_ess = (\<lambda>\<Phi>. \<lambda>x. (\<Phi> x m\<and> ( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))"

  theorem anderson_implies_fuhrmann_aux: "[\<forall>(\<lambda>\<Phi>. \<forall>e(\<lambda>x. (ess \<Phi> x) m\<rightarrow>  \<Phi> x)) ]"
  by (metis refl ess_def)

  theorem anderson_implies_fuhrmann: "[\<forall>(\<lambda>\<Phi>. \<forall>e(\<lambda>x. ((ess \<Phi> x) m\<rightarrow> (fuhrmann_ess \<Phi> x)) )) ]"
  sledgehammer min [remote_satallax] (refl ess_def fuhrmann_ess_def)
  oops
  -- {* by (metis anderson_ess_def fuhrmann_ess_def refl) *}
  -- {* by (metis anderson_ess_def fuhrmann_ess_def refl anderson_implies_fuhrmann_aux) *}

(*<*) 
end
(*>*) 
