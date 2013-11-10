(*<*) 
theory GoedelGodExtensions
imports Main GoedelGod

begin
(*>*)

section {* Further results on G\"odel's God. *}  

text {* G\"odel's God is flawless, that is, he has only positive properties. *}

  theorem Flawless: "[\<forall>(\<lambda>\<phi>. \<forall>(\<lambda>x. (G x m\<rightarrow> (m\<not> (P \<phi>) m\<rightarrow> m\<not> (\<phi> x)))))]"
  sledgehammer [provers = remote_leo2] 
  by (metis A1b G_def) 
  
text {* Moreover, it can be shown that any two God-like beings are equal, that is, 
there is only one God-like being. *}   
  
  theorem Monotheism: "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. (G x m\<rightarrow> (G y m\<rightarrow> (x m= y)))))]"
  sledgehammer [provers = remote_satallax] 
  oops
  (* by (metis Flawless G_def) *)
  
(*<*) 
end
(*>*) 