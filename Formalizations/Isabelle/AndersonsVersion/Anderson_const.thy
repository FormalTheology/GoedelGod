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

Interestingly, while investigating this issue, I found out that Goedel's original manuscript has
a partially erased extra box that has been ignored by everybody so far!


- Varying domain: 
-------------------
Anderson notes that for the definition of necessary existence the "e-quantifier" of Cocchiarella's 
logic should be used (which should correspond to varying domain quantification)
   

- Dependency of A4 and A5:
------------------------------
I find it hard to grasp to which underlying assumptions of second order modal logic Fuhrmann refers,
when he notes that the dependency of A4 and A5 would not be accepted by Anderson. 
As far as I can see, Anderson allows full comprehension and uses S5. 
The only restriction that I have found in Anderson's text is the demand for varying domain 
quantification and I don't see how that could interfere with Hajeks proof. 
(This may be because I misunderstand Hajeks proof. 
I'd be glad if someone could look into this aswell.) 

Bruno: 
varying domain semantics is mentioned when Anderson constructs a model of his axioms
where the modal collapse is falsified (page 7). His footnote 14 also mentions how the quantifiers 
in his natural language axioms and theorems ought to be formalized in this varying domain semantics.

Bruno:
Anderson (1990) also writes (page 2):
'It's worth noticing that there is here an implicit assumption: if we have
defined a predicate, then we can straight-away form a name of the property which it expresses. 
(The technically minded will thus wish to note that it is in effect assumed that anything is 
counted as a property which can be defined by "abstraction on a formula.")'
He is talking about full comprehension here, and indeed there is nothing in Anderson's text that
strongly suggests that he does not wish to admit full comprehension. 
Hajek apparently picks up on this comment by Anderson, and investigate the status variants
with a weaker "cautious" comprehension schema. 
In particular, he (Hajek 1996) investigates Magari's claim that
axioms A4 and A5 are unnecessary, and he concludes that this is:
* false for Gödel's axioms
* true for Gödel' axioms together with an additional axiom called PEP
* true for Anderson's axioms
Hajek (2002, page 7) mentions that Anderson and Gettings (1996) argue that A4 and A5 are needed
if a "finer logic" (i.e. varying domains) is used. 
This is discussed in more detail in his section 4, which I still need to read. 
I also still need to read Anderson and Gettings (1996).
*} 

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<equiv>  ( (\<box> (\<Phi> x ))) ))" 

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>(\<lambda>y. \<Phi> y)))))"

  axiomatization where
    A1:  "[\<forall>(\<lambda>\<Phi>. ((P \<Phi>) m\<rightarrow> m\<not> (P (\<lambda>x. m\<not> (\<Phi> x))) )  )]"  and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]" and
    A3:  "[P G]" 

 
  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists> \<Phi>))]"
  by (metis A1 A2)
         
  corollary C1: "[\<diamond> (\<exists> G)]"
  by (metis A3 T1)

  lemma T2_lem: "[\<forall>(\<lambda>x. \<forall>(\<lambda>\<Phi>. ((G x) m\<and> (ess \<Phi> x)) m\<rightarrow> \<forall>(\<lambda>y. ((G y) m\<rightarrow> \<Phi> y))))]"
  by (metis G_def refl ess_def)
  
  theorem T3: "[\<box> (\<exists> G)]"
  by (metis  A3  G_def sym T1)
  
  corollary C2: "[\<exists> G]"
  by (metis refl T3)
  

  text {* The consistency of the entire theory is confirmed by Nitpick. *}
  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


section {* Provability of A4 and A5 *}

  text {* As noted by Petr Hajek, A4 and A5 can be derived
          from the other axioms and definitions. *}

  theorem A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 
  sledgehammer min [metis] (A3 trans sym C2 G_def)
  by (metis A3 G_def sym trans T3)

  theorem A5: "[P NE]"
  by (metis A2 A3 anderson_ess_def NE_def)

  text{* Fuhrmann remarks that these derivations depend on 
       "meist stillschweigen gemachten Annahmen über die 
       Logik der zweiten Stufe, die Anderson jedoch nicht teilt." *}


section {* Immunity to Modal Collapse *}  
 
  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  nitpick [user_axioms]
  oops


section {* Fuhrmann's Alternative Definition of Essence *}

  definition fuhrmann_ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "fuhrmann_ess = (\<lambda>\<Phi>. \<lambda>x. (\<Phi> x m\<and> ( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
            
  lemma anderson_implies_fuhrmann_aux: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>x. anderson_ess \<Phi> x m\<rightarrow>  \<Phi> x)) ]"
  by (metis refl anderson_ess_def)
  
  theorem anderson_implies_fuhrmann: "[\<forall>(\<lambda>\<Phi>. \<forall> (\<lambda>x. ((anderson_ess \<Phi> x) m\<rightarrow> (fuhrmann_ess \<Phi> x)) )) ]"
  -- {* sledgehammer min [remote_satallax] (refl anderson_ess_def fuhrmann_ess_def) *}
  -- {* by (metis anderson_ess_def fuhrmann_ess_def refl) *}
  oops



(*<*) 
end
(*>*) 
