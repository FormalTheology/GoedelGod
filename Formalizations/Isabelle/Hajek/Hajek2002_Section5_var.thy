
theory Hajek2002_Section5_var
imports Main "../QML_var"

begin

section {* Hajek's Small Emendations *}

text {* This is the theory called AOE'_0 in Definition 12 of Section 5 of Hajek (2002)  *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

text {* In item 2 of the summary in Page 14 of Hajek (2002),
        a different definition for G is written. Here it is assumed that
        this was a mistake. Definition 12 is assumed to be correct.  *}

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv> \<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<leftrightarrow>  ( (\<^bold>\<box> (\<Phi> x ))) )" 

  axiomatization where
    A12:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow>  (\<^bold>\<not> (P ( \<^sup>\<not>\<Psi>) ) )   ))\<rfloor>" and
    A3:  "\<lfloor>P (\<lambda>x. (G x) \<^bold>\<and> (eiw x) ) \<rfloor>" 


subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Provability of A1 *}

text {* This appears as Lemma 3 in Section 4 of Hajek (2002) *} 

  theorem A1: "\<lfloor>\<^bold>\<forall>\<Phi>.( ((P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P (\<^sup>\<not>\<Phi>)) )  )\<rfloor>"
  by (metis A12)

subsection {* Counter-Satisfiability of old A3 *}

text {* The old A3 is not valid anymore. 
        This is counter-intuitive, because it shows that 
        a conjunct of a compound positive property is not necessarily positive.
        This contrasts with Hajek's claim that A12 and the new A3 
        "give a rather pleasant emendation of Gödel's axioms". *}

  theorem OldA3:  "\<lfloor>P G\<rfloor>" 
  nitpick [user_axioms] oops


subsection {* Independence of A2 *}

  theorem A2: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>.( ( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  nitpick [user_axioms, expect = genuine]
  nitpick [satisfy, user_axioms, expect = genuine]
  oops


subsection {* Provability of T1, C1 and T3 *}
  
(* Satallax succeeds, but Leo2 and Metis fail. *)

  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. \<Phi> x))\<rfloor>"
  sledgehammer [provers = remote_satallax remote_leo2, verbose] (A12)
  (* by (metis A12) *)
  sorry

  corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2, verbose] (T1 A3) *)
  by (metis (no_types, lifting) A3 T1)

  lemma L1: "\<lfloor>\<^bold>\<forall>\<^sup>Eu.(( (G u) \<^bold>\<rightarrow> (\<^bold>\<box> ((G u) \<^bold>\<and> (eiw u) ) ) ) ) \<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2, verbose] (G_def T1 C1 A12 A3 sym trans) *)
  by (metis (erased, lifting) A3 G_def)

  axiomatization where
    sym:   "x r y \<longrightarrow> y r x"
    
  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  (* sledgehammer [provers = remote_satallax remote_leo2, verbose, timeout = 200] (L1 C1 T1 A12 A3 sym trans G_def) *)
  by (metis C1 L1 sym)

  axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

  axiomatization where refl: "(x r y) \<longrightarrow> (y r x)"

subsection {* Consistency again *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"
  nitpick [user_axioms] oops


subsection {* Provability of A4 and A5 *}

(* Satallax succeeds, but Metis fails *)

  theorem A4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>" 
  (* sledgehammer min [remote_satallax, verbose] (T3 A3 G_def sym trans) *)
  (* by (metis A3 G_def sym trans T3) *)
  sorry

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess \<Phi> x \<equiv> \<^bold>\<forall>\<Psi>.( ((\<^bold>\<box> (\<Psi> x )) \<^bold>\<leftrightarrow>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE x \<equiv> \<^bold>\<forall>\<Phi>.( ess \<Phi> x \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ey.( \<Phi> y))))"

  
(* Neither a proof nor a counter-model could be found for A5 *)

  theorem A5: "\<lfloor>P NE\<rfloor>"
  (* nitpick [user_axioms, verbose, timeout = 600] *)
  (* sledgehammer min [provers = remote_satallax remote_leo2, verbose, timeout=210] (T3 A3 T1 C1 L1 A12 ess_def NE_def G_def sym trans) *)
  (* by (metis A12 A3 ess_def NE_def) *)
  oops

end
