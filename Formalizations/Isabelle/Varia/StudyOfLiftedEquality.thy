(*<*) 
theory StudyOfLiftedEquality
imports Main

begin
(*>*)

section {* Embedding of QML in HOL *}

  typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for indiviuals"      
  
  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"   

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 65) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 70) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 74) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<longleftrightarrow>" 76) where "\<phi> m\<longleftrightarrow> \<psi> \<equiv> (\<lambda>w. (\<phi> w \<longleftrightarrow> \<psi> w))" 
  abbreviation mequiv2:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 76) where "\<phi> m\<equiv> \<psi> \<equiv> (\<phi> m\<rightarrow> \<psi>) m\<and> (\<psi> m\<rightarrow> \<phi>)" 
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

  no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  

section {* Lifted Leibniz equality @{text "m=1"} *}

text {* First we only concentrate on the type @{text "\<mu>"} and on a straightforward lifting *}

  abbreviation meq1 :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "m=1" 100) where "x m=1 y \<equiv> (\<lambda>w. x = y)"  

  lemma Ref1 : "[\<forall>(\<lambda>x. x m=1 x)]" sledgehammer [remote_leo2] by metis
  lemma Sym1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m=1 y m\<rightarrow> y m=1 x))]" sledgehammer [remote_leo2] by metis 
  lemma Tra1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m=1 y m\<and> y m=1 z) m\<rightarrow> x m=1 z)))]" sledgehammer [remote_leo2] by metis
  lemma Con1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x m=1 y m\<rightarrow> (f x) m=1 (f y))))]"  sledgehammer [remote_leo2] by metis

text {* Hence, @{text "m=1"} is a lifted congruence relation as expected and intended. Moreover, we have that lifted equality
coincides with primitive equality. *}
  
   lemma pri1 : "[x m=1 y] \<Longrightarrow> x = y" sledgehammer [remote_leo2] by metis

section {* Lifted Leibniz equality @{text "m=2"} *}

text {* We extend the above lifting idea to arbitrary types. *} 

  abbreviation meq2 :: "'a \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infixr "m=2" 100) where "x m=2 y \<equiv> (\<lambda>w. x = y)"  

  lemma Ref2 : "[\<forall>(\<lambda>x. x m=2 x)]" sledgehammer [remote_leo2] by metis
  lemma Sym2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m=2 y m\<rightarrow> y m=2 x))]" sledgehammer [remote_leo2] by metis 
  lemma Tra2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m=2 y m\<and> y m=2 z) m\<rightarrow> x m=2 z)))]" sledgehammer [remote_leo2] by metis
  lemma Con2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x m=2 y m\<rightarrow> (f x) m=2 (f y))))]"  sledgehammer [remote_leo2] by metis
  lemma Pri2 : "[x m=2 y] \<Longrightarrow> x = y" sledgehammer [remote_leo2] by metis

text {* Hence, @{text "m=2"} is also a congruence relation as expected and intended, and it also 
coincides with primitive equality. But how about functional and Boolean extensionality. 
It turns out that functional extensionality and the trivial direction of Boolean extensionality 
are valid (though Matis cannot reconstruct the proof for FE2b). *}

  lemma FE2a : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. f m=2 g m\<rightarrow> \<forall>(\<lambda>x. (f x) m=2 (g x))))]" sledgehammer [remote_leo2] by metis
  lemma FE2b : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. (\<forall>(\<lambda>x. (f x) m=2 (g x))) m\<rightarrow> (f m=2 g)))]" sledgehammer [remote_satallax] oops
  lemma BE2a : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. p m=2 q m\<rightarrow> (p m\<longleftrightarrow> q)))]" sledgehammer [remote_leo2] by metis

  lemma BE2b : "\<not> [\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<equiv> q) m\<rightarrow> (p m=2 q)))]" sledgehammer [remote_satallax] oops
  
  lemma eqttest_boolExt1 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<equiv> q) m\<rightarrow> (p mL= q)))]"
  sledgehammer [overlord,  remote_satallax] oops

  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=" 90) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))" 

  

  lemma eqtest0 : "(x m= y) = (x mL= y)"
  sledgehammer [provers = remote_satallax] oops
  
  lemma eqtest1 : "x = y \<Longrightarrow> [x mL= y]"
  sledgehammer [provers = remote_leo2] by metis 
    
  lemma eqtest2 : "[x mL= y] \<Longrightarrow> x = y"
  sledgehammer [provers = remote_satallax remote_leo2] oops
  
  lemma eqtest2 : "[x m= y] \<Longrightarrow> x = y"
  sledgehammer [provers = remote_satallax remote_leo2] by metis
  
  lemma eqtest3 : "[(x m= y) m\<rightarrow> (\<lambda>w. x = y)]"
  sledgehammer [provers = remote_satallax remote_leo2] by metis
  
  lemma eqtest4 : "(x = y) \<Longrightarrow> (x \<equiv> y)"
  sledgehammer [provers = remote_satallax remote_leo2] oops

  lemma eqtest5 : "[x m= y] \<Longrightarrow> [x mL= y]"
  sledgehammer [provers = remote_satallax remote_leo2] by metis
  
  lemma eqtest6 : "[x mL= y] \<Longrightarrow> [x m= y]"
  sledgehammer [provers = remote_satallax remote_leo2] oops
  
(* Lifted Leibniz Equality is a fully extensional congruence relation. *)    
  
  lemma eqttest_refl : "[\<forall>(\<lambda>x. x mL= x)]"
  sledgehammer [provers = remote_leo2] by metis
  
  lemma eqttest_sym : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x mL= y m\<rightarrow> y mL= x))]"
  sledgehammer [provers = remote_leo2] oops

  lemma eqttest_trans : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. ((x mL= y) m\<and> (y mL= z)) m\<rightarrow> (x mL= z))))]"
  sledgehammer [provers = remote_leo2] by metis

  lemma eqttest_congr1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. (x mL= y) m\<rightarrow> ((f x) mL= (f y)))))]"
  sledgehammer [provers = remote_satallax] oops 
  
  lemma eqttest_congr2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>p. (x mL= y) m\<rightarrow> ((p x) m\<rightarrow> (p y)))))]"
  sledgehammer [provers = remote_satallax] by metis 
  
  lemma eqttest_funcExt_triv : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. (f mL= g) m\<rightarrow> \<forall>(\<lambda>x. (f x) mL= (g x))))]"
  sledgehammer [provers = remote_satallax] oops
 
  lemma eqttest_boolExt_triv : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p mL= q) m\<rightarrow> (p m\<longleftrightarrow> q)))]"
  sledgehammer [provers = remote_leo2] oops

  lemma eqttest_funcExt : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. (\<forall>(\<lambda>x. (f x) mL= (g x))) m\<rightarrow> (f mL= g)))]"
  sledgehammer [provers = remote_satallax] oops  
 
(* Interestingly, the nontrivial direction of Boolean extensionality for lifted Leibniz 
equality fails --- this is something to look at. *)    
  
  lemma eqttest_boolExt1 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p mL= q)))]"
  sledgehammer [overlord, remote_satallax] oops
  
  lemma eqttest_boolExt1 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<equiv> q) m\<rightarrow> (p mL= q)))]"
  sledgehammer [overlord,  remote_satallax] oops
  
  lemma eqttest_boolExt2 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m= q) m\<rightarrow> (p mL= q)))]"
  sledgehammer [remote_leo2 remote_satallax] by metis
  
  lemma eqttest_boolExt3 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p mL= q) m\<rightarrow> (p m= q)))]"
  sledgehammer [remote_leo2 remote_satallax] oops
  
  lemma eqttest_boolExt4 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p m= q)))]"
  sledgehammer [remote_leo2 remote_satallax] oops
  
(*<*) 
end
(*>*) 