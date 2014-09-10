(*<*) 
theory LiftedEquality2
imports Main

begin
(*>*)

  
section {* Embedding of QML in HOL *}

  typedecl i    -- "the type for possible worlds" 
  typedecl u    -- "the type for rigid individuals"      
  
  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"   

text {* Note that now \<mu> is lifted too, thus being a type for non-rigid individuals. 
        This gives us extra flexibility and uniformity.
        We can always work enforce rigidity (for individuals or objects of higher types)
        by using the "rigid" predicate defined further down.  *}

  type_synonym \<mu> = "(i \<Rightarrow> u)"
  type_synonym \<sigma> = "(i \<Rightarrow> bool)"

  abbreviation mtrue :: "\<sigma>" ("mT") where "mT \<equiv> (\<lambda>w. True)"    
  abbreviation mfalse :: "\<sigma>" ("mF") where "mF \<equiv> (\<lambda>w. False)"    
  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 65) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 70) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 74) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<longleftrightarrow>" 76) where "\<phi> m\<longleftrightarrow> \<psi> \<equiv> (\<lambda>w. (\<phi> w \<longleftrightarrow> \<psi> w))"  
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

  no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"

  abbreviation meq :: "(i \<Rightarrow> 'a) \<Rightarrow> (i \<Rightarrow> 'a) \<Rightarrow> \<sigma>" (infixr "m=" 100) where "x m= y \<equiv> (\<lambda>w. (x w) = (y w))"  


text {* rigid is a ground predicate allowing us to state that an object is rigid *}

  abbreviation rigid :: "(i \<Rightarrow> 'a) \<Rightarrow> bool" ("rigid") where "(rigid x) \<equiv> \<forall>w1. \<forall>w2. (x w1) = (x w2)"


text {* lrigid is a lifted version of rigid. In contrast to rigid, it can be used inside modal formulas. *}

  abbreviation lrigid :: "(i \<Rightarrow> 'a) \<Rightarrow> \<sigma>" ("lrigid") where "(lrigid x) \<equiv> \<lambda>w. (rigid x)"


text {* As desired, necessitational congruence does not hold in general, as verified by nitpick below *}

  lemma Con : "[\<forall>(\<lambda>\<phi>. \<phi> m= mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))]" nitpick oops 


text {* But necessitational congruence does hold for rigid modal propositions *}

  lemma RigidCon: "\<forall>\<phi>. ((rigid \<phi>) \<and> (rigid mT)) \<longrightarrow> [\<phi> m= mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT)]"
  by metis

text {* With lrigid, we can state essentially the same lemma in the modal language itself *}

  lemma LRigidCon: "[\<forall>(\<lambda>\<phi>. (((lrigid \<phi>) m\<and> (lrigid mT))  m\<rightarrow> (\<phi> m= mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))))]"
  by metis


text {* Note that lrigid extends the expressivity of the underlying modal logic considerably, 
giving it the power to express which objects are rigid. This power is not present in any modal logic that I know.   *}


(*<*) 
end
(*>*) 
