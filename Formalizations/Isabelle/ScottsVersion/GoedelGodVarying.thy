(*<*) 
theory GoedelGodVarying
imports Main 

begin
(*>*)

  typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for indiviuals"      

  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"   

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 51) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 50) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 49) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 48) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  consts eiw :: "i \<Rightarrow> \<mu> \<Rightarrow> bool"  
  axiomatization where nonempty: "\<forall>w. \<exists>x. eiw w x"
  abbreviation mforall_ind :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>i") where "\<forall>i P \<equiv> (\<lambda>w. \<forall>x. eiw w x \<longrightarrow> P x w)"
  abbreviation mexists_ind :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>i") where "\<exists>i P \<equiv> (\<lambda>w. \<exists>x. eiw w x \<and> P x w)"
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=" 52) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>. (\<phi> x m\<rightarrow> \<phi> y))"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  axiomatization where
    A1a: "[\<forall>(\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<rightarrow> m\<not> (P \<Phi>))]" and
    A1b: "[\<forall>(\<lambda>\<Phi>. m\<not> (P \<Phi>) m\<rightarrow> P (\<lambda>x. m\<not> (\<Phi> x)))]" and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>i(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]"

  theorem T1: "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<diamond> (\<exists>i \<Phi>))]"  
  by (metis (lifting) A1a A2)

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<Phi> x))"   

  axiomatization where A3:  "[P G]" 

  corollary C: "[\<diamond> (\<exists>i G)]" 
  by (metis (lifting, no_types) A1a A2 A3) 

  axiomatization where A4:  "[\<forall>(\<lambda>\<Phi>. P \<Phi> m\<rightarrow> \<box> (P \<Phi>))]" 

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x m\<and> \<forall>(\<lambda>\<Psi>. \<Psi> x m\<rightarrow> \<box> (\<forall>i(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y)))"

  theorem T2: "[\<forall>i(\<lambda>x. G x m\<rightarrow> G ess x)]"
  sledgehammer [provers = remote_leo2]
  oops
  
  axiomatization where T2: "[\<forall>i(\<lambda>x. G x m\<rightarrow> G ess x)]"

  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. \<Phi> ess x m\<rightarrow> \<box> (\<exists>i \<Phi>)))"

  axiomatization where A5:  "[P NE]"

  axiomatization where sym: "x r y \<longrightarrow> y r x" 

  theorem T3: "[\<box> (\<exists>i G)]" 
  sledgehammer [provers = remote_leo2]
  oops
  
  axiomatization where T3: "[\<box> (\<exists>i G)]"

  corollary C2: "[\<exists>i G]" 
  by (metis (lifting) A1a A2 A5 sym T3)

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops

  theorem Flawlessness: "[\<forall>(\<lambda>\<Phi>. \<forall>i(\<lambda>x. (G x m\<rightarrow> (m\<not> (P \<Phi>) m\<rightarrow> m\<not> (\<Phi> x)))))]"
  by (metis (lifting, mono_tags) A1b G_def)

  theorem Monotheism: "[\<forall>i(\<lambda>x.\<forall>i(\<lambda>y. (G x m\<rightarrow> (G y m\<rightarrow> (x mL= y)))))]"
  by (metis (lifting) Flawlessness G_def)
  
  axiomatization where refl: "x r x" 

  lemma MC: "[p m\<rightarrow> (\<box> p)]"
  sledgehammer [provers = remote_satallax]
  oops

(*<*) 
end
(*>*) 