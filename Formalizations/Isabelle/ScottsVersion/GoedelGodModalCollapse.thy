(*<*) 
theory GoedelGodModalCollapse
imports Main GoedelGod

begin
(*>*)

section {* Modal Collapse *}  

text {* G\"odel's axioms have been criticized for entailing the so-called 
modal collapse. The prover Satallax \cite{Satallax} confirms this. 
However, sledgehammer does not seem to be able to determine which axioms, 
definitions and previous theorems are used by Satallax;
hence it suggests to call Metis using everything, but this (unsurprisingly) fails.
Attempting to use ``Sledegehammer min'' to minimize Sledgehammer's suggestion does not work.
Nevertheless, calling Metis with T2, T3 and ess_def does work. *} 
  
ToDo: The universal quantifier below has wrong type.

  lemma MC: "[\<forall> (\<lambda>\<Phi>.( \<Phi> m\<Rightarrow> (\<box> \<Phi>)))]"
  using T2 T3 ess_def sym sledgehammer [provers = remote_satallax]
  by (metis T2 T3 ess_def) 


(*<*) 
end
(*>*) 
