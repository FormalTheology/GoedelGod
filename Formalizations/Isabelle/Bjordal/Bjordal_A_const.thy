(*<*) 
theory Bjordal_A_const
imports Main "../QML"

begin
(*>*)

section {* Introduction *}

text {* We verify Frode Bjordal's paper from 1998. 
In this file Bjordal_A.thy we address the claim that
Bjordal's alternative definition D (where God is taken as 
a primitive symbol) implies Gödel's axioms A2, A3 and A4, and
also Gödel's Definition D1. *}

section {* Bjordal's argument *}  
  
text {* Constant symbol @{text "G"} (for 'God') is introduced
here as a primitive constant. Then P is defined using G. This
is Bjordal's definition D. *}

 consts G :: "\<mu> \<Rightarrow> \<sigma>"   
 definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  where "P \<Phi> \<equiv> \<^bold>\<box>(\<^bold>\<forall>x.( G x \<^bold>\<rightarrow> \<Phi> x))" 

text {* Gödel's axioms A2, A3 and A4, and even his definition D1 
can actually be derived from this alternative definition. *}

 theorem A2: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( (P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>x.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" 
 (* sledgehammer [provers = remote_leo2] *)
 by (simp add: P_def) 

 theorem A3: "\<lfloor>P G\<rfloor>"
 (* sledgehammer [provers = remote_leo2] *)
 by (metis P_def)

text {* For proving A4 we need transitivity. *}

 axiomatization where 
  trans: "x r y \<and> y r z \<longrightarrow> x r z"
 
 theorem A4: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis trans P_def)

text {* For proving D1 we need reflexivity . *}

 axiomatization where 
  refl: "x r x" 

 theorem D1: "\<lfloor>(G x) \<^bold>\<leftrightarrow> ( \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<Phi> x))\<rfloor>" 
(*  sledgehammer [provers = remote_leo2 remote_satallax] *) 
 by (metis refl P_def)


(*<*) 
end
(*>*) 