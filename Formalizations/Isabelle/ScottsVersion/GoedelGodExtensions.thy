(*<*) 
theory GoedelGodExtensions
imports Main GoedelGod

begin
(*>*)

section {* Further results on G\"odel's God. *}  

text {* Lifted Leibniz equality is introduced. *}

  abbreviation mequals :: "'a \<Rightarrow> 'a \<Rightarrow> \<sigma>" (infixr "m=" 90) where "x m= y \<equiv> \<forall>(\<lambda> \<phi>.(\<phi> x m\<rightarrow> \<phi> y))" 

text {* G\"odel's God is flawless, that is, he has only positive properties. *}

  theorem Flawless: "[\<forall>(\<lambda>\<phi>. \<forall>(\<lambda>x. (G x m\<rightarrow> (m\<not> (P \<phi>) m\<rightarrow> m\<not> (\<phi> x)))))]"
  sledgehammer [provers = remote_leo2 remote_satallax] by (metis A1b G_def) 
  
text {* Moreover, it can be shown that any two God-like beings are equal, that is, 
there is only one God-like being. *}   
  
  theorem Monotheism: "[\<forall>(\<lambda>x. \<forall>(\<lambda>y. (G(x) m\<rightarrow> (G(y) m\<rightarrow> (x m= y)))))]"
  sledgehammer [provers = remote_leo2] by (metis Flawless G_def) 
  
text {* Add-on: We briefly show that lifted Leibniz equality indeed denotes equality. *}  

  lemma eqtest1: "x = y \<Longrightarrow> [x m= y]"
  sledgehammer [provers = remote_leo2] by metis 
    
  lemma eqtest2: "[x m= y] \<Longrightarrow> x = y"
  sledgehammer [provers = remote_satallax] oops

text {* m= is an a fully extensional congruence relation. *}    
  
  lemma eqttest_refl : "[\<forall>(\<lambda>x. x m= x)]"
  sledgehammer [provers = remote_leo2] by metis
  
  lemma eqttest_sym : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. x m= y m\<rightarrow> y m= x))]"
  sledgehammer [provers = remote_satallax] oops

  lemma eqttest_trans : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>z. (x m= y m\<and> y m= z) m\<rightarrow> x m= z)))]"
  sledgehammer [provers = remote_leo2] by metis

  lemma eqttest_congr : "[\<forall>(\<lambda>x.\<forall>(\<lambda>y.\<forall>(\<lambda>f. x m= y m\<rightarrow> (f x m= f y))))]"
  sledgehammer [provers = remote_leo2] oops 
  
  lemma eqttest_funcExt_triv : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. f m= g m\<rightarrow> \<forall>(\<lambda>x. f x m\<rightarrow> g x)))]"
  sledgehammer [provers = remote_leo2] oops

  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 73) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  
  lemma eqttest_boolext_triv : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. p m= q m\<rightarrow> p m\<equiv> q))]"
  sledgehammer [provers = remote_leo2] oops

  lemma eqttest_funcExt : "[\<forall>(\<lambda>f.\<forall>(\<lambda>g. \<forall>(\<lambda>x. f x m\<rightarrow> g x) m\<rightarrow> f m= g))]"
  sledgehammer [provers = remote_leo2] by metis  
  
  lemma eqttest_boolext : "[\<forall>(\<lambda>p.\<forall>(\<lambda>q. p m\<equiv> q m\<rightarrow> p m= q))]"
  sledgehammer [provers = remote_leo2] by metis
  
(*<*) 
end
(*>*) 