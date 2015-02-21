(*<*) 
theory NoEvilVarying
imports Main "../QML_Var"

begin
(*>*)

  text {* Constant symbol @{text "P"} (G\"odel's `Positive') is declared. *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  
  axiomatization where
    A1a: "[\<forall>(\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<rightarrow> m\<not> (P \<Phi>))]" and
    A2:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P \<Phi> m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow> P \<Psi>))]"
 
section {* There is no Evil *}    

 text {* Based on a idea suggested by Chad Brown (private communication), we prove that 
 there is no evil. This argument defines an evil-like entity as an entity that has all
 non-positive properties. Chad Brown's argument is as follows: "Define D x: x is a devil if 
 x has all negative properties [opposite of positive]. The fact that the empty property is 
 negative follows easily from Axiom 1a and 2. It's then possible to argue that there is no 
 devil as follows: We want to prove [\<box> (m\<not>(\<exists> E))]. Let w be a world and u be a related 
 world. Assume there is a devil d at world u. Since the empty property is negative, d must 
 have the empty property at world u. That is, we have a proof of false. QED."*}
 
 text {* An property if negative if and only if it is not positive. *}  
 definition N :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  where "N = (\<lambda>\<Phi>. m\<not> (P \<Phi>))" 
 
 text {* An entity is Evil-like if  and only if it has all negative properties. *} 
  definition E :: "\<mu> \<Rightarrow> \<sigma>" where "E = (\<lambda>x. \<forall>(\<lambda>\<Phi>. (N \<Phi>) m\<rightarrow> \<Phi> x))"   

 text {* The argument can be proven by leo2, however, proof reconstruction fails. *}
  theorem NoEvil: "[\<box> (m\<not>(\<exists> E))]" 
  -- {* sledgehammer [provers = remote\_leo2](N_def E_def A1a A2) *}
  -- {* by (metis N_def E_def A1a A2) *}
  oops

(*<*) 
end
(*>*) 