(*<*) 
theory GoedelGodExtensions
imports Main GoedelGod

begin
(*>*)

section {* Additional Results on G\"odel's God. *}  

text {* G\"odel's God is flawless: (s)he does not have non-positive properties. *}

  theorem Flawlessness: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>x. (G x m\<rightarrow> (m\<not> (P \<Phi>) m\<rightarrow> m\<not> (\<Phi> x)))))]"
  sledgehammer [provers = remote_leo2] 
  by (metis A1b G_def) 
  
text {* There is only one God: any two God-like beings are equal. *}   
  
  theorem Monotheism: "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. (G x m\<rightarrow> (G y m\<rightarrow> (x mL= y)))))]"
  sledgehammer [provers = remote_leo2]
  by (metis Flawlessness G_def)
(*<*) 
end
(*>*) 