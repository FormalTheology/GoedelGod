
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
            "P' = (\<lambda>\<Phi>. \<exists>(\<lambda>\<Psi>.((P \<Psi>) m\<and> (\<box> (\<forall>e(\<lambda>x.((\<Psi> x) m\<rightarrow> (\<Phi> x) ) )))  ) ))     "

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ( (\<box> (\<Phi> x ))) m\<equiv> P \<Phi> ))" 

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess = (\<lambda>\<Phi>. \<lambda>x. (( (\<forall>(\<lambda>\<Psi>. ((\<box> (\<Psi> x )) m\<equiv>  \<box>(\<forall>e(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE = (\<lambda>x. \<forall>(\<lambda>\<Phi>. ess \<Phi> x m\<rightarrow> (\<box> (\<exists>e(\<lambda>y. \<Phi> y)))))"

  axiomatization where
    A12:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. ( (P \<Phi>) m\<and> \<box> (\<forall>e(\<lambda>x. \<Phi> x m\<rightarrow> \<Psi> x))) m\<rightarrow>  (m\<not> (P (\<lambda>y.( m\<not> (\<Psi> y)) ) ) )   ))]" and
    A3:  "[P (\<lambda>x. (G x m\<and> eiw x) ) ]" and
    GOD: "[G g m\<and> eiw g]" 



text {* Interesting fact: as in "Hajek2002_Section4_var.thy",  A4 and A5 were still not needed to prove T3! *}
 

subsection {* Independence of A4 *}

text {* Hájek writes P instead of the first occurrence of P' in his definition of A4. 
        However, the the rest of his text makes it clear that this was a typo. *} 

   axiomatization where euc: "(w r v \<and> w r u) \<longrightarrow> v r u" and ref: "x r x" and
   trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"
  
lemma L6 : "[\<forall>(\<lambda>\<Phi>.((P' \<Phi>) m\<rightarrow> (\<box> (P' \<Phi>) )))]"
(*sledgehammer min [remote_leo2, verbose, timeout = 120] (A12 A3 G_def Hajek2002_Section5_P2_var.trans P'_def bot_bool_def euc ext induct_conj_def nonempty ref)
leo2 finds a proof*)
(*by (metis A3 G_def Hajek2002_Section5_P2_var.trans P'_def euc ext  nonempty ref)*)
oops

axiomatization where  L6 : "[\<forall>(\<lambda>\<Phi>.((P' \<Phi>) m\<rightarrow> (\<box> (P' \<Phi>) )))]"

lemma L7: "[ \<forall>(\<lambda>x. G x m\<rightarrow> ess G x )]"
 
 (*sledgehammer [provers=remote_leo2 remote_satallax, verbose, timeout = 120]  
 nitpick[user_axioms]
 nitpick[user_axioms, satisfy]

status unclear
*)
oops
axiomatization where L7:  "[\<forall>(\<lambda>x. G x m\<rightarrow> ess G x)]"

lemma L8: "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. \<forall>(\<lambda>x. ((ess \<Phi> x) m\<and> (ess \<Psi> x)) m\<rightarrow> \<box> (\<forall>e(\<lambda>y.(\<Phi> y m\<rightarrow> \<Psi> y))))))]"
 (*nitpick[user_axioms]
 nitpick[user_axioms, satisfy] 
 sledgehammer min [provers=remote_leo2 remote_satallax, verbose, timeout=120] (sym trans ess_def euc) 

 Status unclear
 *)
oops

axiomatization where L8:  "[\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. \<forall>(\<lambda>x. ((ess \<Phi> x) m\<and> (ess \<Psi> x)) m\<rightarrow> \<box> (\<forall>e(\<lambda>y.(\<Phi> y m\<rightarrow> \<Psi> y))))))]" 
lemma L9: "[P' NE]" 
(*
  nitpick[user_axioms]
 nitpick[user_axioms, satisfy] 
sledgehammer[provers = remote_leo2 remote_satallax]
*)
oops
axiomatization where L9: "[P' NE]"
  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

end
