
theory Anderson_var
imports Main "../QML_var"

begin


section {* Anderson's Ontological Argument -- varying domain (individuals) *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )" 

  axiomatization where
    A1:  "\<lfloor>\<^bold>\<forall>\<Phi>. (((P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"  and
    A2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>" and
    A3:  "\<lfloor>P G\<rfloor>" 

subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of T1, C and T3 *}
  
  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. \<Phi> x))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2)
  
  corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3)

  text {* we only need axiom B here *}
  axiomatization where sym: "x r y \<longrightarrow> y r x"
    
  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A1 A2 A3 sym G_def)

subsection {* Consistency again (now with sym) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of A4 and A5 *}

  text {* As noted by Petr Hajek, A4 and A5 can be derived
          from the other axioms and definitions. *}
  
  text {* for A4 we need transitivity *}
  axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

  theorem A4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>" 
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A3 G_def sym trans T3)

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess \<Phi> x \<equiv> \<^bold>\<forall>\<Psi>.( ((\<^bold>\<box> (\<Psi> x )) \<^bold>\<leftrightarrow>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE x \<equiv> \<^bold>\<forall>\<Phi>.( ess \<Phi> x \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ey.( \<Phi> y))))"

  theorem A5: "\<lfloor>P NE\<rfloor>"
  by (metis A2 A3 ess_def NE_def)


subsection {* Consistency again (now with sym and trans) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.((\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)))\<rfloor>"
  nitpick [user_axioms] oops

subsection {* Varia *}

lemma HAJEK: "\<lfloor>P ( \<lambda>x. (G x \<^bold>\<and> eiw x))\<rfloor>"
by (metis A2 A3 A5)


  lemma PEP: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( (P \<Phi> \<^bold>\<and> (\<lambda>x. (\<Phi> = \<Psi>))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  (* nitpick *)
  by metis

  lemma PEP_Leibniz: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. ((P \<Phi> \<^bold>\<and> (\<^bold>\<forall>Q.(Q \<Phi> \<^bold>\<rightarrow> Q \<Psi>  ))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  (* nitpick *)
  by metis

  lemma weak_congruence: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. ((P \<Phi> \<^bold>\<and> \<^bold>\<box>(\<lambda>x. (\<Phi> = \<Psi>))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] *)
  by (metis A2) 


end
