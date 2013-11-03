(*<*) 
theory GoedelGodExtensions
imports Main GoedelGod

begin
(*>*)

section {* Further results on G\"odel's God. *}  

  abbreviation mequals :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "m=" 90) where "x m= y \<equiv> \<Pi> (\<lambda> \<phi>.(\<phi> x m\<Rightarrow> \<phi> y))" 

text {* G\"odel's God is flawless, that is, he has no negative properties. *}

  theorem Flawless: "[\<Pi> (\<lambda>\<phi>. \<forall> (\<lambda>x. (G x m\<Rightarrow> (m\<not> (P \<phi>) m\<Rightarrow> m\<not> (\<phi> x)))))]"
  sledgehammer [provers = remote_leo2] by (metis A1b G_def) 
  
text {* Moreover, it can be shown that any two God-like beings are (Leibniz-)equal, that is there is 
there only one God-like being. *}   
  
  theorem Monotheism: "[\<forall> (\<lambda>x. \<forall> (\<lambda>y. (G(x) m\<Rightarrow> (G(y) m\<Rightarrow> (x m= y)))))]"
  sledgehammer [provers = remote_leo2] by (metis C sym T2 ess_def) 
  
text {* Add-on: We briefly show that Leibniz equality denotes equality. *}  

  lemma test2: "x = y \<Longrightarrow> [x m= y]"
  sledgehammer [provers = remote_leo2] 
  by metis 
    
  lemma test1: "[x m= y] \<Longrightarrow> x = y"
  sledgehammer [provers = remote_satallax] oops

 
(*<*) 
end
(*>*) 