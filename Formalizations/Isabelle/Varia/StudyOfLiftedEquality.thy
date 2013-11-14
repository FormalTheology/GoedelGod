(*<*) 
theory StudyOfLiftedEquality
imports Main

begin
(*>*)

section {* Leibniz equality is the same as primitive equality in HOL (with Henkin or standard semantics) *}

  lemma L1 : "\<forall>x y. ((\<forall>p. (p(x) \<longrightarrow> p(y))) \<longrightarrow> (x = y))"
  apply (rule allI)+
  apply (rule impI)
  apply (erule_tac x = "\<lambda>u. x = u" in allE)
  by simp

  theorem Leibniz1 : "\<forall>x y. ((x = y) \<longleftrightarrow> (\<forall>p. (p(x) \<longrightarrow> p(y))))"  
  by (metis L1)

  theorem Leibniz2 : "\<forall>x y. ((x = y) = (\<forall>p. (p(x) \<longrightarrow> p(y))))"  
  by (metis L1)
  
  theorem Leibniz3 : "(\<lambda> x y. (x = y)) = (\<lambda> x y. (\<forall>p. (p(x) \<longrightarrow> p(y))))"  
  by (metis L1)
  
section {* Embedding of QML in HOL *}

  typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for indiviuals"      
  
  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"   

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
  
  
section {* Lifted Leibniz equality is the same as lifted primitive equality in HOL *}  
  
  lemma LL1 : "[\<forall>(\<lambda>x. \<forall>(\<lambda>y. ((\<forall>(\<lambda>p. (p(x) m\<rightarrow> p(y)))) m\<rightarrow> (\<lambda>w. x = y))))]"
  apply (rule allI)+
  apply (rule impI)
  apply (erule_tac x = "\<lambda>u. (\<lambda>w. x = u)" in allE)
  by simp

  theorem LLeibniz1 : "[\<forall>(\<lambda>x. \<forall>(\<lambda>y. ((\<lambda>w. x = y) m\<longleftrightarrow> (\<forall>(\<lambda>p. (p(x) m\<rightarrow> p(y)))))))]"  
  by (metis LL1)
  
  theorem LLeibniz2 : "\<forall>x y. [\<lambda>w. x = y] \<longleftrightarrow> [\<forall>(\<lambda>p. (p(x) m\<rightarrow> p(y)))]"  
  by (metis LL1)
  
  theorem LLeibniz3 : "\<forall>x y. [\<lambda>w. x = y] = [\<forall>(\<lambda>p. (p(x) m\<rightarrow> p(y)))]"  
  by (metis LL1)

section {* Lifted primitive equality *}

text {* First we only concentrate on the type @{text "\<mu>"} and on a straightforward lifting *}

  abbreviation meq1 :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "m=1" 100) where "x m=1 y \<equiv> (\<lambda>w. x = y)"  

  lemma Ref1 : "[\<forall>(\<lambda>x. x m=1 x)]" sledgehammer [remote_leo2] by metis
  lemma Sym1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m=1 y m\<rightarrow> y m=1 x))]" sledgehammer [remote_leo2] by metis 
  lemma Tra1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m=1 y m\<and> y m=1 z) m\<rightarrow> x m=1 z)))]" sledgehammer [remote_leo2] by metis
  lemma Con1a : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x m=1 y m\<rightarrow> (f x) m=1 (f y))))]"  sledgehammer [remote_leo2] by metis
  lemma Con1b : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>p. x m=1 y m\<rightarrow> (p x) m\<longleftrightarrow> (p y))))]"  sledgehammer [remote_leo2] by metis

  
text {* Hence, @{text "m=1"} is a lifted congruence relation as expected and intended. Moreover, we have that lifted equality
coincides with primitive equality. *}
  
  lemma Pri1 : "\<forall> x y. [x m=1 y] = (x = y)" sledgehammer [remote_leo2] by metis  

text {* We extend the above lifting idea to arbitrary types. *} 

  abbreviation meq2 :: " 'a \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infixr "m=2" 100) where "x m=2 y \<equiv> (\<lambda>w. x = y)"  

  lemma Ref2 : "[\<forall>(\<lambda>x. x m=2 x)]" sledgehammer [remote_leo2] by metis
  lemma Sym2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m=2 y m\<rightarrow> y m=2 x))]" sledgehammer [remote_leo2] by metis 
  lemma Tra2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m=2 y m\<and> y m=2 z) m\<rightarrow> x m=2 z)))]" sledgehammer [remote_leo2] by metis
  lemma Pri2 : "\<forall> x y. [x m=2 y] = (x = y)" sledgehammer [remote_leo2] by metis

text {* We again check for congruence. Both congruence properties are still valid. *}

  lemma Con2a : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x m=2 y m\<rightarrow> (f x) m=2 (f y))))]"  sledgehammer [remote_leo2] by metis
  lemma Con2b : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>p. x m=2 y m\<rightarrow> (p x) m\<longleftrightarrow> (p y))))]"  sledgehammer [remote_leo2] by metis

text {* However, this is not what we would like. To see this see the following property; this is 
certainly not what we want! *}

  lemma Con2c : "[\<forall>(\<lambda>\<phi>. (\<phi> m=2 mT) m\<rightarrow> ((\<box> \<phi>) m\<longleftrightarrow> (\<box> mT)))]"  sledgehammer [remote_leo2] by metis

text {* Hence, @{text "m=2"} is also a congruence relation, but this time this not intended.
@{text "m=2"} also still coincides primitive equality. But how about functional and Boolean extensionality?
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

  lemma Con3c : "[\<forall>(\<lambda>\<phi>. \<phi> m=3 mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))]"  sledgehammer [remote_leo2] by metis
  lemma BE3b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p m=3 q)))]" nitpick oops
  
text {* Here is an alternative definition of lifted primitive equality for type \<sigma> which does suffer 
from the above problems. *}  

  abbreviation meq4 :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m=4" 100) where "x m=4 y \<equiv> (\<lambda>w. ((x w) = (y w)))"  
 
  lemma Ref4 : "[\<forall>(\<lambda>x. x m=4 x)]" sledgehammer [remote_leo2] by metis
  lemma Sym4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m=4 y m\<rightarrow> y m=4 x))]" sledgehammer [remote_leo2] by metis 
  lemma Tra4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m=4 y m\<and> y m=4 z) m\<rightarrow> x m=4 z)))]" sledgehammer [remote_leo2] by metis
  lemma Pri4 : "\<forall> x y. [x m=4 y] = (x = y)" sledgehammer [remote_leo2] oops
  lemma BE4a : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m=4 q) m\<rightarrow> (p m\<longleftrightarrow> q)))]" sledgehammer [remote_leo2] by metis
  lemma BE4b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p m=4 q)))]" sledgehammer [remote_leo2] by metis

text {* @{text "m=4"} invalidates the lifted congruance property. This is what what actually want.*}  

  lemma Con4a : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. (x m=4 y) m\<rightarrow> (f x) m=4 (f y))))]" nitpick oops  
  lemma Con4b : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>p. x m=4 y m\<rightarrow> (p x) m\<longleftrightarrow> (p y))))]" nitpick oops  
  lemma Con4c : "[\<forall>(\<lambda>\<phi>. \<phi> m=4 mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))]"  nitpick oops 
 

section {* Lifted Leibniz equality *}

  abbreviation meqL1 :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=1" 100) where "x mL=1 y \<equiv>  \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))"  

  lemma RefL1 : "[\<forall>(\<lambda>x. x mL=1 x)]" sledgehammer [remote_leo2] by metis
  lemma SymL1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x mL=1 y m\<rightarrow> y mL=1 x))]" sledgehammer [remote_leo2] oops
  lemma TraL1 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x mL=1 y m\<and> y mL=1 z) m\<rightarrow> x mL=1 z)))]" sledgehammer [remote_leo2] by metis
  lemma ConL1a : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x mL=1 y m\<rightarrow> (f x) mL=1 (f y))))]"  sledgehammer [remote_leo2] oops
  lemma ConL1b : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>p. x mL=1 y m\<rightarrow> (p x) m\<longleftrightarrow> (p y))))]"  sledgehammer [remote_leo2] oops
  lemma PriL1 : "\<forall> x y. [x mL=1 y] = (x = y)" sledgehammer [remote_satallax] oops

text {* Ok, fine @{text "mL=1"} validates all these properties. And this is as intended for type \<mu>. 
How about extending it to arbitrary types? *}  

  abbreviation meqL2 :: "'a \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infixr "mL=2" 100) where "x mL=2 y \<equiv>  \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))"  

  lemma RefL2 : "[\<forall>(\<lambda>x. x mL=2 x)]" sledgehammer [remote_leo2] by metis
  lemma SymL2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x mL=2 y m\<rightarrow> y mL=2 x))]" sledgehammer [remote_leo2] oops
  lemma TraL2 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x mL=2 y m\<and> y mL=2 z) m\<rightarrow> x mL=2 z)))]" sledgehammer [remote_leo2] by metis
  lemma PriL2 : "\<forall> x y. [x mL=2 y] = (x = y)" sledgehammer [remote_satallax] oops

  lemma FEL2a : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. f mL=2 g m\<rightarrow> \<forall>(\<lambda>x. (f x) mL=2 (g x))))]" sledgehammer [remote_leo2] oops
  lemma FEL2b : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. (\<forall>(\<lambda>x. (f x) mL=2 (g x))) m\<rightarrow> (f mL=2 g)))]" sledgehammer [remote_satallax] oops
  lemma BEL2a : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. p mL=2 q m\<rightarrow> (p m\<longleftrightarrow> q)))]" sledgehammer [remote_leo2] oops

text {* So far that is fine. But again, the non-trivial direction of Boolean extensionality fails. *}

  lemma BEL2b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p mL=2 q)))]" nitpick oops

text {* And unfortunately, we have congruence which we don't want in the general case. *}
  lemma ConL2a : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x mL=2 y m\<rightarrow> (f x) mL=2 (f y))))]"  sledgehammer [remote_leo2] oops
  lemma ConL2b : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>p. x mL=2 y m\<rightarrow> (p x) m\<longleftrightarrow> (p y))))]"  sledgehammer [remote_leo2] oops
  lemma ConL2c : "[\<forall>(\<lambda>\<phi>. \<phi> mL=2 mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))]"  sledgehammer [remote_leo2] oops

text {* Let's focus on lifted equality for type \<sigma> only. The problem remains the same. *} 

  abbreviation meqL3 :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "mL=3" 100) where "x mL=3 y \<equiv>  \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))"  

  lemma BEL3b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p mL=3 q)))]" nitpick oops
  lemma ConL3c : "[\<forall>(\<lambda>\<phi>. \<phi> mL=3 mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))]"  sledgehammer [remote_leo2] oops

text {* Let's try to modify the Leibniz definition. Again we cosinder only the case for \<sigma>. *}

  abbreviation meqL4 :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "mL=4" 100) where "x mL=4 y \<equiv>  (\<lambda>w. (\<forall>(\<lambda>\<phi>.((\<phi> (x w) m\<rightarrow> (\<phi> (y w)))))) w)"

  lemma RefL4 : "[\<forall>(\<lambda>x. x mL=4 x)]" sledgehammer [remote_leo2] by metis
  lemma SymL4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x mL=4 y m\<rightarrow> y mL=4 x))]" sledgehammer [remote_leo2] oops
  lemma TraL4 : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x mL=4 y m\<and> y mL=4 z) m\<rightarrow> x mL=4 z)))]" sledgehammer [remote_leo2] by metis
  lemma PriL4 : "\<forall> x y. [x mL=4 y] = (x = y)" sledgehammer [remote_satallax] oops
  lemma BEL4a : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. p mL=4 q m\<rightarrow> (p m\<longleftrightarrow> q)))]" sledgehammer [remote_leo2] oops
  lemma BEL4b : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<longleftrightarrow> q) m\<rightarrow> (p mL=4 q)))]" sledgehammer [remote_leo2] oops

text {* So far that is fine. Moreover, it turns out that congruence fails as intended. *}

  lemma ConL4a : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x mL=4 y m\<rightarrow> (f x) mL=4 (f y))))]" nitpick oops
  lemma ConL4b : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>p. x mL=4 y m\<rightarrow> (p x) m\<longleftrightarrow> (p y))))]" nitpick oops  
  lemma ConL34 : "[\<forall>(\<lambda>\<phi>. \<phi> mL=4 mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))]" nitpick oops   


section {* Correspondences *}

  lemma Cor1 : "(x m=1 y) = (x mL=1 y)" sledgehammer [remote_satallax] oops
  lemma Cor2 : "(x m=2 y) = (x mL=2 y)" sledgehammer [remote_satallax] oops
  lemma Cor3 : "(x m=3 y) = (x mL=3 y)" sledgehammer [remote_satallax] oops
  lemma Cor4 : "(x m=4 y) = (x mL=4 y)" sledgehammer [remote_satallax] oops

section {* Preliminary Conclusion *}

text {*
The reasonable options for lifted equalities are as follows. If we are just interested in lifted equality 
on base type \<mu>, then @{text "x m= y \<equiv> (\<lambda>w. x = y)"} or @{text "x mL= y \<equiv>  \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))"} are 
reasonable options (and we have @{text "(x m= y) = (x mL= y)"}. Congruence, which holds, does not seem 
problematic in this case.

If we are interested in lifted equality on higher types, let's say on type \<sigma> (modal propositions), 
then we have to be very careful. Choosing again
@{text "x m= y \<equiv> (\<lambda>w. x = y)"} or @{text "x mL= y \<equiv>  \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))"} implies
that we can prove congruence, and hence also @{text "[\<forall>(\<lambda>\<phi>. \<phi> m=/mL= mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))]"}, 
which looks like a form of modal collapse. Moreover, we have that the non-trivial direction of 
Boolean extensionality fails for both @{text "m=/mL="}.

As an alternative we may thus use
@{text "x m= y \<equiv> (\<lambda>w. ((x w) = (y w)))"} or 
@{text "x mL= y \<equiv>  (\<lambda>w. (\<forall>(\<lambda>\<phi>.((\<phi> (x w) m\<rightarrow> (\<phi> (y w)))))) w)"}; we again have 
that @{text "(x m= y) = (x mL= y)"}.
For these forms of lifted equalities it holds that congruence fails (which is good and we also don't
get @{text "[\<forall>(\<lambda>\<phi>. \<phi> m=/mL= mT m\<rightarrow> (\<box> \<phi>) m\<longleftrightarrow> (\<box> mT))]"} as a theorem). Moreover, now Boolean 
extensionality holds again. Thus, these two choices of lifted equalities seem more appropriate
for type \<sigma>. 

Further discussion is needed! *}
(*<*) 
end
(*>*) 