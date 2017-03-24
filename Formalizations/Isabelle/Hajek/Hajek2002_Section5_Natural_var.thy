theory Hajek2002_Section5_Natural_var
imports Main "../QML_var"

begin

section {* Hajek's Small Emendations *}

text {* This is the theory called AOE'' in Definition 13 of Section 5 of Hajek (2002)  *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

text {* P' is Hajek' P#. The symbol "#" is not allowed by Isabelle. 
        In Hajek's definition, a possibilistic universal quantifier was used.
        However, careful reading gives strong reason to believe that this was just a typo
        and an actualistic quantifier was intended. *}

  definition P' :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
            "P' \<Phi> \<equiv> \<^bold>\<exists>\<Psi>.(((P \<Psi>) \<^bold>\<and> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.(((\<Psi> x) \<^bold>\<rightarrow> (\<Phi> x) ) )))  ) )     "

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( ( (\<^bold>\<box> (\<Phi> x ))) \<^bold>\<leftrightarrow> P' \<Phi> )" 

  axiomatization where
    A12:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. (( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow>  (\<^bold>\<not> (P (\<lambda>y.( \<^bold>\<not> (\<Psi> y)) ) ) )   ))\<rfloor>" and
    A3:  "\<lfloor>P G \<rfloor>" 




subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops

subsection {* Provability of T1, C1 and L1 *}
  
(* Satallax succeeds, but Leo2 and Metis fail. *)

  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. \<Phi> x))\<rfloor>"
  (* sledgehammer [provers = remote_satallax remote_leo2, verbose] (A12) *)
  (* by (metis A12) *)
  sorry

  corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2, verbose] (T1 A3) *)
  by (metis (no_types, lifting) A3 T1)

  lemma L1: "\<lfloor>\<^bold>\<forall>\<^sup>Eu.(( (G u) \<^bold>\<rightarrow> (\<^bold>\<box> (G u) ) ) ) \<rfloor>"
  (* sledgehammer [remote_satallax, verbose, timeout = 60] (G_def A3 P'_def) *)
  (* sledgehammer [remote_leo2, verbose, timeout = 60] (G_def A3 P'_def) *)
  by (metis (erased, lifting) A3 G_def P'_def)


subsection {* Provability of T3 *}

  axiomatization where sym:   "x r y \<longrightarrow> y r x"

(* when given (T1 L3 A3 A4 sym trans G_def P'_def) as facts,
   Leo2 succeeds, but Satallax and Metis fail.
   Sledgehammer with Leo2 minimize the list of facts to (T1 A3 sym G_def P'_def). 
   With this minimized list of facts, 
   Metis succeeds but Satallax still fails.
   Interestingly, Leo2 (or Sledgehammer) seems to be adding the 
   extra fact "ext" to obtain its proofs. Nevertheless, 
   Metis succeeds when called without "ext". Maybe Metis assumes it implicitly.
   Satallax still fails even when "ext" is explicitly provided. 
   To find out why Satallax is failing, this should be compared to T3 in "Hajek2002_Section4_var.thy".
   There Satallax succeeds. *)
  
  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  (* sledgehammer min [remote_satallax, verbose, timeout = 60] (T1 L3 A3 A4 sym trans G_def P'_def) *)
  (* sledgehammer min [remote_satallax, verbose, timeout = 60] (T1 L3 A3 A4 sym trans G_def P'_def ext) *)
  (* sledgehammer min [remote_leo2, verbose] (T1 L3 A3 A4 sym trans G_def P'_def) *)
  (* sledgehammer min [remote_leo2, verbose] (T1 A3 sym G_def P'_def) *)
  (* sledgehammer min [remote_satallax, verbose] (T1 A3 sym G_def P'_def) *)
  (* sledgehammer min [remote_satallax, verbose] (T1 A3 sym G_def P'_def ext) *)
  by (metis T1 A3 sym G_def P'_def)
   
text {* Interesting fact: as in "Hajek2002_Section4_var.thy",  A4 and A5 were still not needed to prove T3! *}
 

subsection {* Independence of A4 *}

text {* Hájek writes P instead of the first occurrence of P' in his definition of A4. 
        However, the the rest of his text makes it clear that this was a typo. *} 

  lemma A4 : "\<lfloor>\<^bold>\<forall>\<Phi>.(((P' \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<box> (P' \<Phi>) )))\<rfloor>"
  nitpick [user_axioms]
  nitpick [satisfy, user_axioms]
  oops

  axiomatization where A4 : "\<lfloor>\<^bold>\<forall>\<Phi>.(((P' \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<box> (P' \<Phi>) )))\<rfloor>"

  axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

text {* A4 seems necessary to prove the interesting lemma L3 *}

  lemma Aux1: "\<lfloor>\<^bold>\<forall>\<Phi>.( (P \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ey.(((G y) \<^bold>\<rightarrow> (\<^bold>\<box>(\<Phi> y)) )) ) ) \<rfloor>"
  by (metis G_def P'_def)

  lemma L3: "\<lfloor>\<^bold>\<forall>\<Phi>.( (P \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ey.(((G y) \<^bold>\<rightarrow> (\<Phi> y))) ) ) )\<rfloor>"
  (* sledgehammer min [remote_satallax] (Aux1 P'_def trans sym A4) *)
  by (metis Aux1 P'_def trans sym A4)


subsection {* Consistency again (now with A4, sym, trans and refl) *}

  axiomatization where refl: "((x r y) \<longrightarrow> (y r x))"

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Independence of A5 *}

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess \<Phi> x \<equiv> \<^bold>\<forall>\<Psi>.( ((\<^bold>\<box> (\<Psi> x )) \<^bold>\<leftrightarrow>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE x \<equiv> \<^bold>\<forall>\<Phi>.( ess \<Phi> x \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ey.( \<Phi> y))))"

text {* The Old A5 is still independent, as before. *}

  lemma OldA5: "\<lfloor>P NE\<rfloor>"
  nitpick [user_axioms]
  nitpick [user_axioms, satisfy]
  oops

text {* However, the status of the new A5 is inconclusive.
        Neither a proof nor a counter-model could be found so far. *}

  lemma A5: "\<lfloor>P' NE\<rfloor>"
  (* nitpick [user_axioms] *)
  (* nitpick [user_axioms, satisfy] *)
  (* sledgehammer [provers = metis remote_satallax remote_leo2, verbose] (A12 A3 A4 G_def P'_def ess_def NE_def sym trans) *)
  oops

  axiomatization where A5: "\<lfloor>P' NE\<rfloor>"


subsection {* Consistency again (with A5) *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"
  nitpick [user_axioms] oops




subsection {* Analysis of Pages 13 and 14: ToDo *}

theorem A3_e:  "\<lfloor>P (\<lambda>x. (G x \<^bold>\<and> eiw x) ) \<rfloor>"
sledgehammer[provers = remote_leo2 remote_satallax, verbose]
oops



(* ToDo: Theorem 6 and Lemmas 6, 7, 8 and 9 in Hajek 2002 deserve to be investigated *)


 lemma L6: "\<lfloor>\<^bold>\<forall>\<Phi>.( P' \<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> (P' \<Phi>)))\<rfloor>"
 by (metis A4)
 
 consts g :: "\<mu>" 
 axiomatization where for_simplicity: "\<lfloor>G g \<^bold>\<and> eiw g\<rfloor>"


 (* Satallax finds a proof *)
 lemma L7: "\<lfloor>ess G g\<rfloor>"
 (* sledgehammer [remote_satallax remote_leo2, verbose] (A12 A3 A5 Aux1 C1 G_def Hajek2002_Section5_Natural_var.sym Hajek2002_Section5_Natural_var.trans L1 L3 L6 NE_def P'_def T1 T3 ess_def for_simplicity nonempty) *)
 oops

 (* Satallax finds a proof *)
 lemma L8: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( \<^bold>\<forall>u.( (ess \<Phi> u \<^bold>\<and> (ess \<Psi> u)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y)))))\<rfloor>"
 (* sledgehammer min [remote_satallax, verbose] (A12 A3 A5 Aux1 C1 G_def Hajek2002_Section5_Natural_var.sym Hajek2002_Section5_Natural_var.trans L1 L3 L6 NE_def P'_def T1 T3 ess_def for_simplicity nonempty) *)
 oops

 (* Satallax finds a proof *)
 corollary C1: "\<lfloor>\<^bold>\<forall>\<Phi>.( ess \<Phi> g \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey.( G y \<^bold>\<rightarrow> \<Phi> y)))\<rfloor>"
 (* sledgehammer min [remote_satallax, verbose] (A12 A3 A5 Aux1 C1 G_def Hajek2002_Section5_Natural_var.sym Hajek2002_Section5_Natural_var.trans L1 L3 L6 NE_def P'_def T1 T3 ess_def for_simplicity nonempty) *)
 oops

 lemma L9: "\<lfloor>P' NE\<rfloor>"
 by (metis A5) 


 theorem T6: "todo"
 oops

end
