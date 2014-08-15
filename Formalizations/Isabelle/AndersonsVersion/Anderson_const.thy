(*<*) 
theory Anderson_const
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

  axiomatization where 
  sym: "x r y \<longrightarrow> y r x" and
  refl: "x r x" and
  trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"


text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  
section {* Anderson's Ontological Argument -- constant domain*}

text{* 

Adapted to follow Anderson's original paper more closely.

- Axiom 1: 
---------------------
The dropped implication of Axiom 1 is not mentioned in Anderson's formalization 
(only in the semi-formal text)

- Definition of essence:
------------------------- 
In Anderson's definition of essence the implication on the right side of the equivalence is not in 
the scope of a box. There is only a box for the left side of the equivalence. This does not seem to 
change anything: Metis still succeeds to prove all formulae. What surprises me is that Hajek, 
Fitting, and Fuhrmann put a box in front of the the implication in the definition of essence. 
This box does not appear in Anderson's original paper (neither in the text nor in his formalization). 
According to nitpick those two definitions are not equivalent.

Fuhrmann's definition of essence has the missing conjunct, 
whereas Anderson has it neither in the text nor in his formalization. 
But it should be easy to prove that Andersons definition implies the missing conjunct: 
Just instantiate the consequent of the implication with the essence of x. 
Then, by the equivalence follows that x has the essence.  
(This seems too trivial, did I miss something?) 
(Metis finds a proof aswell)

- Varying domain: 
-------------------
Anderson notes that for the definition of necessary existence the "e-quantifier" of Cocchiarella's 
logic should be used (which should correspond to varying domain quantification)

- Positivity:
------------------
To circumvent the constraints of second-order logic Anderson defines positivity indirectly:
He introduces the predicate defective(x) and then defines positive(P) as "not P implies defective". 
Where "A implies B" (for predicates) means "box forall(x) A(x) implies B(x)". 
When I change the formalization accordingly, everything still goes through, 
but the cardinalities of the counter model for modal collapse differ 
(2 possible worlds, 1 individual instead of 2 possible worlds, 2 individuals).     

- Dependency of A4 and A5:
------------------------------
I find it hard to grasp to which underlying assumptions of second order modal logic Fuhrmann refers,
when he notes that the dependency of A4 and A5 would not be accepted by Anderson. 
As far as I can see, Anderson allows full comprehension and uses S5. 
The only restriction that I have found in Anderson's text is the demand for varying domain 
quantification and I don't see how that could interfere with Hajeks proof. 
(This may be because I misunderstand Hajeks proof. 
I'd be glad if someone could look into this aswell.) 
*} 

  consts Defective :: "\<mu> \<Rightarrow> \<sigma>" 

 --{*
  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  *}
  
  definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
  "P = (\<lambda>\<Phi>. \<box> (\<forall>(\<lambda>x. (m\<not> (\<Phi>(x))) m\<rightarrow> Defective(x))))"
  
  
  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<equiv>  ( (\<box> (\<Phi> x ))) ))" 

--{* In Anderson's version as presented by Fuhrmann, 
     "ess" has the extra conjunct introduced by Scott,
     which is missing here. There is discrepancy between Fitting's 
     and Fuhrmann's presentations of Anderson's proof. Christoph: Yes, the exra
     conjunct is indeed missing in Fitting's presentation of Anderson's proof; in fact,
     there is even a sentence "The Scott addition that the essence of an object actually
     apply to the object, is dropped."
     Leon: The extra conjunct is missing in Anderson's formalization aswell. Still, there is 
     discrepancy because the second box in the definiton of essence is not present in Anderson's
     formalization.
     *}

  definition fitting_ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "fitting_ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 

  definition anderson_ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "anderson_ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  (\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
 
  definition fuhrmann_ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "fuhrmann_ess = (\<lambda>\<Phi>. \<lambda>x. (\<Phi> x m\<and> ( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 

 
            
  theorem fitting_implies_fuhrmann: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>x. fitting_ess \<Phi> x m\<rightarrow>  \<Phi> x)) ]"
  by (metis Anderson_const.refl fitting_ess_def)
  
  text {* The two box definition of essence is not equivalent to the original definition
          in Anderson's paper. *}
  theorem fitting_ess_equiv_ess: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>x. anderson_ess \<Phi> x m\<equiv> fitting_ess \<Phi> x)) ]"
  nitpick[user_axioms] oops
  
            
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. anderson_ess \<Phi> x m\<rightarrow> (\<box> (\<exists>(\<lambda>y. \<Phi> y)))))"

  axiomatization where

--{* Fuhrmann also presents a slightly different axiom A1; Christoph: That was a mistake 
     by Leon, I assume. I changed this from [\<forall>(\<lambda>\<Phi>. ( (P \<Phi>)) m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))))] 
     to [\<forall>(\<lambda>\<Phi>. ( (P (\<lambda>x. m\<not> (\<Phi> x)))) m\<rightarrow> m\<not> (P \<Phi>))]. *}

    A1:  "[\<forall>(\<lambda>\<Phi>. ( (P (\<lambda>x. m\<not> (\<Phi> x)))) m\<rightarrow> m\<not> (P \<Phi>))]" and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" and
    A3:  "[P G]" 

 
  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists> \<Phi>))]"
  by (metis A1 A2)
         
  corollary C1: "[\<diamond> (\<exists> G)]"
  by (metis A3 T1)

  lemma T2_lem: "[\<forall>(\<lambda>x. \<forall>(\<lambda>\<Phi>. ((G x) m\<and> ( anderson_ess \<Phi> x)) m\<rightarrow> \<forall>(\<lambda>y. ((G y) m\<rightarrow> \<Phi> y))))]"
  by (metis G_def Anderson_const.refl anderson_ess_def)
  
  theorem T3: "[\<box> (\<exists> G)]"
  by (metis  A3  G_def sym T1)
  
  corollary C2: "[\<exists> G]"
  by (metis refl T3)
  

text {* The consistency of the entire theory is confirmed by Nitpick. *}
   lemma True 
   nitpick [satisfy, user_axioms, expect = genuine] oops


section {* Modal Collapse *}  
 
  --{* Nitpick generates a counter-model with the same cardinalities used by Anderson. *}
  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms]
  oops

section {* Additional results: *}

text{* As noted by Petr Hajek, A4 and A5 can be derived
       from the other axioms and definitions. *}

  theorem A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 
  by (metis A3 G_def sym trans T3)

  theorem A5: "[P NE]"
  by (metis A2 A3 anderson_ess_def NE_def)


text{* Fuhrmann remarks that these derivations depend on 
       "meist stillschweigen gemachten Annahmen über die 
       Logik der zweiten Stufe, die Anderson jedoch nicht teilt." *}

--{* It should be checked whether the version formalized here is really Anderson's version. 
     It could be a modification by Hajek presented by Fitting. *}



(*<*) 
end
(*>*) 
