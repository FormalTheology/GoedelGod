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
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

  no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  

section {* Lifted primitive equality *}

text {* First we only concentrate on the type @{text "\<mu>"} and on a straightforward lifting *}

  abbreviation meq1 :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "m=1" 100) where "x m=1 y \<equiv> (\<lambda>w. x = y)"  

  lemma Ref1 : "[\<forall>(\<lambda>x. x m=1 x)]" sledgehammer [remote_leo2] by metis
  lemma Sym1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m=1 y m\<rightarrow> y m=1 x))]" sledgehammer [remote_leo2] by metis 
  lemma Tra1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m=1 y m\<and> y m=1 z) m\<rightarrow> x m=1 z)))]" sledgehammer [remote_leo2] by metis
  lemma Con1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x m=1 y m\<rightarrow> (f x) m=1 (f y))))]"  sledgehammer [remote_leo2] by metis

text {* Hence, @{text "m=1"} is a lifted congruence relation as expected and intended. Moreover, we have that lifted equality
coincides with primitive equality. *}
  
  lemma Pri1 : "\<forall> x y. [x m=1 y] = (x = y)" sledgehammer [remote_leo2] by metis  

text {* We extend the above lifting idea to arbitrary types. *} 

  abbreviation meq2 :: " 'a \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infixr "m=2" 100) where "x m=2 y \<equiv> (\<lambda>w. x = y)"  

  lemma Ref2 : "[\<forall>(\<lambda>x. x m=2 x)]" sledgehammer [remote_leo2] by metis
  lemma Sym2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m=2 y m\<rightarrow> y m=2 x))]" sledgehammer [remote_leo2] by metis 
  lemma Tra2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m=2 y m\<and> y m=2 z) m\<rightarrow> x m=2 z)))]" sledgehammer [remote_leo2] by metis
  lemma Con2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x m=2 y m\<rightarrow> (f x) m=2 (f y))))]"  sledgehammer [remote_leo2] by metis
  lemma Pri2 : "\<forall> x y. [x m=2 y] = (x = y)" sledgehammer [remote_leo2] by metis

text {* Hence, @{text "m=2"} is also a congruence relation as expected and intended, and it also 
coincides with primitive equality. But how about functional and Boolean extensionality?
It turns out that (lifted) functional extensionality and the trivial direction of Boolean extensionality 
are valid (though Matis cannot reconstruct the proof for FE2b). Note: Whenever you an 'oops' 
just put the mouse pointer before the oops to get relevant information in the README window of jedit. *}

  lemma FE2a : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. f m=2 g m\<rightarrow> \<forall>(\<lambda>x. (f x) m=2 (g x))))]" sledgehammer [remote_leo2] by metis
  lemma FE2b : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. (\<forall>(\<lambda>x. (f x) m=2 (g x))) m\<rightarrow> (f m=2 g)))]" sledgehammer [remote_satallax] oops
  lemma BE2a : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. p m=2 q m\<rightarrow> (p m\<longleftrightarrow> q)))]" sledgehammer [remote_leo2] by metis

text {* However, the non-trivial direction of Boolean extensionality does not hold (Just put the mouse 
pointer after the call to Nitpick to get relevant information in the README window of jedit. *}

  lemma BE2b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p m=2 q)))]" nitpick oops

text {* Let's focus on lifted equality for type \<sigma> only. The problem remains the same. *} 

  abbreviation meq3 :: " \<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m=3" 100) where "x m=3 y \<equiv> (\<lambda>w. x = y)"  

  lemma BE3b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p m=3 q)))]" nitpick oops
  
text {* Here is an alternative definition of lifted primitive equality for type \<sigma> which does suffer 
from this problem. *}  

  abbreviation meq4 :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m=4" 100) where "x m=4 y \<equiv> (\<lambda>w. ((x w) = (y w)))"  
 
  lemma Ref4 : "[\<forall>(\<lambda>x. x m=4 x)]" sledgehammer [remote_leo2] by metis
  lemma Sym4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m=4 y m\<rightarrow> y m=4 x))]" sledgehammer [remote_leo2] by metis 
  lemma Tra4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m=4 y m\<and> y m=4 z) m\<rightarrow> x m=4 z)))]" sledgehammer [remote_leo2] by metis
  lemma Pri4 : "\<forall> x y. [x m=4 y] = (x = y)" sledgehammer [remote_leo2] oops
  lemma BE4a : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m=4 q) m\<rightarrow> (p m\<longleftrightarrow> q)))]" sledgehammer [remote_leo2] by metis
  lemma BE4b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p m=4 q)))]" sledgehammer [remote_leo2] by metis

text {* Unfortuntely, this @{text "m=4"} invalidates the lifted congruance property. *}  

  lemma Con4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. (x m=4 y) m\<rightarrow> (f x) m=4 (f y))))]" nitpick oops 

text {* Unfortuntely, this @{text "m=4"} invalidates the lifted congruence property. *}  

section {* Lifted Leibniz equality *}

  abbreviation meqL1 :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=1" 100) where "x mL=1 y \<equiv>  \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))"  

  lemma RefL1 : "[\<forall>(\<lambda>x. x mL=1 x)]" sledgehammer [remote_leo2] by metis
  lemma SymL1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x mL=1 y m\<rightarrow> y mL=1 x))]" sledgehammer [remote_leo2] oops
  lemma TraL1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x mL=1 y m\<and> y mL=1 z) m\<rightarrow> x mL=1 z)))]" sledgehammer [remote_leo2] by metis
  lemma ConL1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x mL=1 y m\<rightarrow> (f x) mL=1 (f y))))]"  sledgehammer [remote_leo2] oops
  lemma PriL1 : "\<forall> x y. [x mL=1 y] = (x = y)" sledgehammer [remote_satallax] oops

text {* Ok, fine @{text "mL=1"} validates all these properties. How about extensionality then? *}  

  abbreviation meqL2 :: "'a \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infixr "mL=2" 100) where "x mL=2 y \<equiv>  \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))"  

  lemma RefL2 : "[\<forall>(\<lambda>x. x mL=2 x)]" sledgehammer [remote_leo2] by metis
  lemma SymL2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x mL=2 y m\<rightarrow> y mL=2 x))]" sledgehammer [remote_leo2] oops
  lemma TraL2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x mL=2 y m\<and> y mL=2 z) m\<rightarrow> x mL=2 z)))]" sledgehammer [remote_leo2] by metis
  lemma ConL2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x mL=2 y m\<rightarrow> (f x) mL=2 (f y))))]"  sledgehammer [remote_leo2] oops
  lemma PriL2 : "\<forall> x y. [x mL=2 y] = (x = y)" sledgehammer [remote_satallax] oops

  lemma FEL2a : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. f mL=2 g m\<rightarrow> \<forall>(\<lambda>x. (f x) mL=2 (g x))))]" sledgehammer [remote_leo2] oops
  lemma FEL2b : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. (\<forall>(\<lambda>x. (f x) mL=2 (g x))) m\<rightarrow> (f mL=2 g)))]" sledgehammer [remote_satallax] oops
  lemma BEL2a : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. p mL=2 q m\<rightarrow> (p m\<longleftrightarrow> q)))]" sledgehammer [remote_leo2] oops

text {* So far that is fine. But again, the non-trivial direction of Boolean extensionality fails. *}

  lemma BEL2b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p mL=2 q)))]" nitpick oops

text {* Let's focus on lifted equality for type \<sigma> only. The problem remains the same. *} 

  abbreviation meqL3 :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "mL=3" 100) where "x mL=3 y \<equiv>  \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))"  

  lemma BEL3b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p mL=3 q)))]" nitpick oops

text {* Let's try to modify the Leibniz definition. Again we cosinder only the case for \<sigma>. *}

  abbreviation meqL4 :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "mL=4" 100) where "x mL=4 y \<equiv>  (\<lambda>w. (\<forall>(\<lambda>\<phi>.((\<phi> (x w) m\<rightarrow> (\<phi> (y w)))))) w)"

  lemma RefL4 : "[\<forall>(\<lambda>x. x mL=4 x)]" sledgehammer [remote_leo2] by metis
  lemma SymL4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x mL=4 y m\<rightarrow> y mL=4 x))]" sledgehammer [remote_leo2] oops
  lemma TraL4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x mL=4 y m\<and> y mL=4 z) m\<rightarrow> x mL=4 z)))]" sledgehammer [remote_leo2] by metis
  lemma PriL4 : "\<forall> x y. [x mL=4 y] = (x = y)" sledgehammer [remote_satallax] oops
  lemma BEL4a : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. p mL=4 q m\<rightarrow> (p m\<longleftrightarrow> q)))]" sledgehammer [remote_leo2] oops
  lemma BEL4b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p mL=4 q)))]" sledgehammer [remote_leo2] oops

text {* So far that is fine. But now again the congruence property fails. *}

  lemma ConL4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x mL=4 y m\<rightarrow> (f x) mL=4 (f y))))]" nitpick oops 

section {* Correspondences *}

  lemma Cor1 : "(x m=1 y) = (x mL=1 y)" sledgehammer [remote_satallax] oops
  lemma Cor2 : "(x m=2 y) = (x mL=2 y)" sledgehammer [remote_satallax] oops
  lemma Cor3 : "(x m=3 y) = (x mL=3 y)" sledgehammer [remote_satallax] oops
  lemma Cor4 : "(x m=4 y) = (x mL=4 y)" sledgehammer [remote_satallax] oops

section {* Preliminary Conclusion *}

Lifted equality (be it primitive or Leibniz) are fine for type \<mu> (extensionality is not an issue).

However, when considering lifted equalities also for predicate or functional types (be it primitive or 
Leibniz) then we should be careful. The above versions either miss the non-trivial 
direction of Boolean extensionality or they miss congruence. But missing the non-trivial direction of
Boolean extensionality is probably even what we want (needs to be discussed)? 
(*<*) 
end
(*>*) 