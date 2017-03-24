
theory Hajek2002_Section5_P2_var
imports Main "../QML_var"

begin

section {* Hajek's Small Emendations *}

text {* This is the theory called AOE'_0 in Definition 13 of Section 5 of Hajek (2002)  *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"
  consts g :: "\<mu>"

text {* P' is Hajek' P#. The symbol "#" is not allowed by Isabelle. 
        In Hajek's definition, a possibilistic universal quantifier was used.
        However, careful reading gives strong reason to believe that this was just a typo
        and an actualistic quantifier was intended. *}

  definition P' :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
            "P' \<Phi> \<equiv> \<^bold>\<exists>\<Psi>.( ((P \<Psi>) \<^bold>\<and> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.(((\<Psi> x) \<^bold>\<rightarrow> (\<Phi> x) ) )))  ) )"

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( ( (\<^bold>\<box> (\<Phi> x ))) \<^bold>\<leftrightarrow> P \<Phi> )" 

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess \<Phi> x \<equiv> \<^bold>\<forall>\<Psi>.( ((\<^bold>\<box> (\<Psi> x )) \<^bold>\<leftrightarrow>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE x \<equiv> \<^bold>\<forall>\<Phi>.( ess \<Phi> x \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ey.( \<Phi> y))))"

  axiomatization where
    A12:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.(( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow>  (\<^bold>\<not> (P (\<^sup>\<not>\<Psi>) ) ) ))\<rfloor>" and
    A3:  "\<lfloor>P (\<lambda>x. (G x \<^bold>\<and> eiw x) ) \<rfloor>" and
    GOD: "\<lfloor>G g \<^bold>\<and> eiw g\<rfloor>" 



text {* Interesting fact: as in "Hajek2002_Section4_var.thy",  A4 and A5 were still not needed to prove T3! *}
 

subsection {* Independence of A4 *}

text {* Hájek writes P instead of the first occurrence of P' in his definition of A4. 
        However, the the rest of his text makes it clear that this was a typo. *} 

   axiomatization where euc: "(w r v \<and> w r u) \<longrightarrow> v r u" and ref: "x r x" and
   trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"
  
lemma L6 : "\<lfloor>\<^bold>\<forall>\<Phi>.(((P' \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<box> (P' \<Phi>) )))\<rfloor>"
(*sledgehammer min [remote_leo2, verbose, timeout = 120] (A12 A3 G_def Hajek2002_Section5_P2_var.trans P'_def bot_bool_def euc ext induct_conj_def nonempty ref)
leo2 finds a proof*)
(*by (metis A3 G_def Hajek2002_Section5_P2_var.trans P'_def euc ext  nonempty ref)*)
oops

axiomatization where  L6 : "\<lfloor>\<^bold>\<forall>\<Phi>.(((P' \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<box> (P' \<Phi>) )))\<rfloor>"

lemma L7: "\<lfloor> \<^bold>\<forall>x.( G x \<^bold>\<rightarrow> ess G x )\<rfloor>"
 
 (*sledgehammer [provers=remote_leo2 remote_satallax, verbose, timeout = 120]  
 nitpick[user_axioms]
 nitpick[user_axioms, satisfy]

status unclear
*)
oops
axiomatization where L7:  "\<lfloor>\<^bold>\<forall>x.( G x \<^bold>\<rightarrow> ess G x)\<rfloor>"

lemma L8: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( \<^bold>\<forall>x.( ((ess \<Phi> x) \<^bold>\<and> (ess \<Psi> x)) \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ey.((\<Phi> y \<^bold>\<rightarrow> \<Psi> y))))))\<rfloor>"
 (*nitpick[user_axioms]
 nitpick[user_axioms, satisfy] 
 sledgehammer min [provers=remote_leo2 remote_satallax, verbose, timeout=120] (sym trans ess_def euc) 

 Status unclear
 *)
oops

axiomatization where L8:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( \<^bold>\<forall>x.( ((ess \<Phi> x) \<^bold>\<and> (ess \<Psi> x)) \<^bold>\<rightarrow> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ey.((\<Phi> y \<^bold>\<rightarrow> \<Psi> y))))))\<rfloor>" 
lemma L9: "\<lfloor>P' NE\<rfloor>" 
(*
  nitpick[user_axioms]
 nitpick[user_axioms, satisfy] 
sledgehammer[provers = remote_leo2 remote_satallax]
*)
oops
axiomatization where L9: "\<lfloor>P' NE\<rfloor>"
  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

end
