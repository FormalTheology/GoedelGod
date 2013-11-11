(*<*) 
theory GoedelGodLeibnizEquality
imports Main GoedelGod GoedelGodExtensions

begin
(*>*)

section {* Lifted Leibniz Equality *}

text {* Lifted Leibniz equality is introduced. *}

  abbreviation mLeibeq :: "'a \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infixr "mL=" 90) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>.((\<phi> x) m\<rightarrow> (\<phi> y)))" 

text {* Lifted Leibniz equality indeed denotes equality. *}  

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
  
text {* Lifted Leibniz Equality is a fully extensional congruence relation. *}    
  
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
 
  lemma eqttest_boolExt_triv : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p mL= q) m\<rightarrow> (p m\<equiv> q)))]"
  sledgehammer [provers = remote_leo2] oops

  lemma eqttest_funcExt : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. (\<forall>(\<lambda>x. (f x) mL= (g x))) m\<rightarrow> (f mL= g)))]"
  sledgehammer [provers = remote_satallax] oops  
 
text {* Interestingly, the nontrivial direction of Boolean extensionality for lifted Leibniz 
equality fails --- this is something to look at. *}    
  
  lemma eqttest_boolExt1 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<equiv> q) m\<rightarrow> (p mL= q)))]"
  sledgehammer [remote_leo2 remote_satallax] oops
  
  lemma eqttest_boolExt2 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m= q) m\<rightarrow> (p mL= q)))]"
  sledgehammer [remote_leo2 remote_satallax] by metis
  
  lemma eqttest_boolExt3 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p mL= q) m\<rightarrow> (p m= q)))]"
  sledgehammer [remote_leo2 remote_satallax] oops
  
  lemma eqttest_boolExt4 : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. (p m\<equiv> q) m\<rightarrow> (p m= q)))]"
  sledgehammer [remote_leo2 remote_satallax] oops
  
(*<*) 
end
(*>*) 