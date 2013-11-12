(*<*) 
theory GoedelGodModalCollapse
imports Main GoedelGod

begin
(*>*)

section {* Modal Collapse *}  

text {* G\"odel's axioms have been criticized for entailing the so-called 
modal collapse. The prover Satallax \cite{Satallax} confirms this. 
However, sledgehammer is not able to determine which axioms, 
definitions and previous theorems are used by Satallax;
hence it suggests to call Metis using everything, but this (unsurprinsingly) fails.
Attempting to use `Sledegehammer min' to minimize Sledgehammer's suggestion does not work.
Calling Metis with @{text "T2"}, @{text "T3"} and @{text "ess_def"} also does not work. *} 

  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  sledgehammer [provers = remote_satallax] oops
  (* by (metis T2 T3 ess_def) *)
(*<*) 
end
(*>*) 
