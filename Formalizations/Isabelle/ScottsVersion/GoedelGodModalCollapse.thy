(*<*) 
theory GoedelGodModalCollapse
imports Main GoedelGod

begin
(*>*)

section {* Modal Collapse *}  

text {* It has been criticized that G\"odel's axioms entail the so-called 
modal collapse. The prover Satallax \cite{Satallax} can show this. 
Sledgehammer does not seem to be able to determine which axioms have been used by Satallax;
hence it suggests to call Metis with all axioms, definitions and theorems, which fails.
Furthermore, ``Sledegehammer min'' does not work.
Nevertheless, calling Metis with T2 T3 and ess_def does work. *} 
  
  lemma MC: "[p m\<Rightarrow> (\<box> p)]"
  using T2 T3 ess_def sym sledgehammer [provers = remote_satallax]
  by (metis T2 T3 ess_def) 


(*<*) 
end
(*>*) 
