(*<*) 
theory Bjordal_B_var
imports Main "../QML_var"

begin
(*>*)

section {* Introduction *}

text {* We verify Frode Bjordal's paper from 1998. 
In this file Bjordal_B.thy we address the claim that
Gödel's axioms A2, A3 and A4, and
also Gödel's Definition D1 imply alternative definition D 
(where God is taken as a primitive symbol) implies  *}
  
section {* Bjordal's argument *}  
 
text {* Constant symbol @{text "P"} (for 'Positive') is introduced
here as a primitive constant. Then G is defined using P. This is
Gödel's definition D1. *}  

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  
  definition G :: "\<mu> \<Rightarrow> \<sigma>"  where "G x \<equiv> \<^bold>\<forall>\<Phi>. (P \<Phi> \<^bold>\<rightarrow> \<Phi> x)" 

text {* We postulate Gödel's axioms A2, A3 and A4. *}

 axiomatization where
  A2: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( (P \<Phi> \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" and     
  A3: "\<lfloor>P G\<rfloor>" and
  A4: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>"


text {* We then show, using two lemmas, that Bjordal's definition 
D is implied. *}

 lemma Case1: "\<lfloor>\<^bold>\<forall>\<Phi>.( (\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.( G x \<^bold>\<rightarrow> \<Phi> x))) \<^bold>\<rightarrow> P \<Phi>)\<rfloor>"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis A2 A3) 

 lemma Case2: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.( G x \<^bold>\<rightarrow> \<Phi> x))))\<rfloor>"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis A4 G_def) 

 theorem D1: "\<lfloor>P \<Phi> \<^bold>\<leftrightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.( G x \<^bold>\<rightarrow> \<Phi> x))\<rfloor>"
 (* sledgehammer [provers = remote_leo2 remote_satallax] *)
 by (metis Case1 Case2) 

(*<*) 
end
(*>*) 