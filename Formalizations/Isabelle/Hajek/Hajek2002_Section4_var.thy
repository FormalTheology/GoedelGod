
theory Hajek2002_Section4_var
imports Main "../QML_var"

begin

section {* Hajek's Small Emendations *}

text {* This is the theory called AOE' in Section 4 of Hajek (2002)  *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where 
            "G x \<equiv>  \<^bold>\<forall>\<Phi>. ((\<^bold>\<box> (\<Phi> x ))  \<^bold>\<leftrightarrow>  ( \<^bold>\<exists>\<Psi>.(( (P \<Psi>) \<^bold>\<and> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Psi> x \<^bold>\<rightarrow> \<Phi> x))) )))  )" 

  axiomatization where
    A12:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. (( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow>  (\<^bold>\<not> (P (\<lambda>y.( \<^bold>\<not> (\<Psi> y)) ) ) )   ))\<rfloor>" and
    A3:  "\<lfloor>P G\<rfloor>" 


subsection {* Consistency *}

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Provability of A1 *}

text {* This appears as Lemma 3.1 in Section 4 of Hajek (2002) *} 

  theorem A1: "\<lfloor>\<^bold>\<forall>\<Phi>.( ((P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P (\<lambda>x. \<^bold>\<not> (\<Phi> x))) )  )\<rfloor>"
  by (metis A12)


subsection {* Counter-Satisfiability of A2 *}

  theorem A2: "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. (( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex.( \<Phi> x \<^bold>\<rightarrow> \<Psi> x))) \<^bold>\<rightarrow> P \<Psi>))\<rfloor>"
  nitpick [user_axioms, expect = genuine] oops


subsection {* Provability of T1, L1 and C1 *}

text {* T1 and L1 appear as Lemmas 3.2 and 3.3 in Hajek 2002 *}

(* Satallax succeeds, but Leo2 and Metis fail *)

  theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. \<Phi> x))\<rfloor>"
  (* sledgehammer [remote_satallax remote_leo2] (A12) *)
  (* by (metis A12) *)
  sorry
  
  corollary C1: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  by (metis T1 A3)

  lemma L1: "\<lfloor>\<^bold>\<forall>\<^sup>Eu.(( (G u) \<^bold>\<rightarrow> (\<^bold>\<box> (G u) ) ) ) \<rfloor>"
  by (metis (erased, lifting) A3 G_def)


subsection {* Provability of T3 *}

  axiomatization where sym:   "x r y \<longrightarrow> y r x"

(* Satallax succeeds, but Leo2 and Metis fail on the full list of facts.
   Metis succeeds, but Satallax and Leo2 fail on the minimized list of facts. *)
  
  theorem T3: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
  (* sledgehammer min [remote_satallax, verbose] (T1 L3 A3 A4 sym trans G_def) *)
  (* sledgehammer min [remote_leo2, verbose] (T1 L3 A3 A4 sym trans G_def) *)
  (* sledgehammer min [remote_satallax, verbose] (T1 A3 sym G_def) *)
  (* sledgehammer min [remote_leo2, verbose] (T1 A3 sym G_def) *)
  (* by (metis T1 L3 A3 A4 sym trans G_def) *)
  by (metis T1 A3 G_def sym)

text {* Interesting fact: A4 and A5 were not needed to prove T3 above! *}

subsection {* Independence of A4 *}
 
  lemma A4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>" 
  nitpick [user_axioms, expect = genuine]
  nitpick [user_axioms, expect = genuine, satisfy]
  oops

text {* But A4 seems necessary to prove the interesting lemma L3 *}

  axiomatization where A4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( P \<Phi> \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>" 

  axiomatization where trans: "((x r y) \<and> (y r z)) \<longrightarrow> (x r z)"

text {* Lemma L3 appears as Lemma 3.4 in Hajek 2002 and Aux1 appears in the proof of Lemma 3.4 *}

  lemma Aux1: "\<lfloor>\<^bold>\<forall>\<Phi>. ((P \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<forall>\<^sup>Ey.(((G y) \<^bold>\<rightarrow> (\<^bold>\<box>(\<Phi> y)) )) ) ) \<rfloor>"
  by (metis G_def)

  lemma L3: "\<lfloor>\<^bold>\<forall>\<Phi>.( (P \<Phi>) \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ey.(((G y) \<^bold>\<rightarrow> (\<Phi> y))) ) ) )\<rfloor>"
  (* sledgehammer min [remote_satallax] (Aux1 trans sym A4) *)
  (* sledgehammer min [remote_satallax] (Aux1 trans sym) *)
  (* sledgehammer min [remote_leo2] (Aux1 trans sym) *)
  (* by (metis Aux1 trans sym) *)
  by (metis Aux1 trans sym A4)


subsection {* Consistency again (now with sym, trans and refl) *}

  axiomatization where refl: "((x r y) \<longrightarrow> (y r x))"

  lemma True 
  nitpick [satisfy, user_axioms, expect = genuine] oops


subsection {* Immunity to Modal Collapse *}  
 
  lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>.(\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>))\<rfloor>"
  nitpick [user_axioms] oops


subsection {* Independence of A5 *}

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where 
            "ess \<Phi> x \<equiv>  \<^bold>\<forall>\<Psi>.( ((\<^bold>\<box> (\<Psi> x )) \<^bold>\<leftrightarrow>  \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ey.( \<Phi> y \<^bold>\<rightarrow> \<Psi> y))))" 
       
  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where 
            "NE x \<equiv> \<^bold>\<forall>\<Phi>.( ess \<Phi> x \<^bold>\<rightarrow> (\<^bold>\<box> (\<^bold>\<exists>\<^sup>Ey.( \<Phi> y))))"

  lemma A5: "\<lfloor>P NE\<rfloor>"
  nitpick [satisfy, user_axioms, expect = genuine]
  nitpick [user_axioms, expect = genuine]
  oops

end
