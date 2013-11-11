(*<*) 
theory GoedelGodExtensions
imports Main GoedelGod

begin
(*>*)

section {* Additional Results on G\"odel's God. *}  

text {* G\"odel's God is flawless: (s)he does not have a non-positive property. *}

  theorem Flawlessness: "[\<forall>(\<lambda>\<phi>. \<forall>(\<lambda>x. (G x m\<rightarrow> (m\<not> (P \<phi>) m\<rightarrow> m\<not> (\<phi> x)))))]"
  sledgehammer [provers = remote_leo2] 
  by (metis A1b G_def) 
  
text {* There is only one God: any two God-like beings are equal. *}   
  
  theorem Monotheism: "[\<forall>(\<lambda>x.\<forall>(\<lambda>y. (G x m\<rightarrow> (G y m\<rightarrow> (x m= y)))))]"
  sledgehammer [provers = remote_satallax remote_leo2] 
  oops
  (* by (metis Flawlessness G_def) *)
  
(*<*) 
end
(*>*) 