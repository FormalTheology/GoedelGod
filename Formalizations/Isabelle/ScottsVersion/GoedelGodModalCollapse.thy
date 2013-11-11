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
Attempting to use `Sledegehammer min' to minimize Sledgehammer's suggestion does not work.
Nevertheless, calling Metis with @{text "T2"}, @{text "T3"} and @{text "ess_def"} does work. *} 

  lemma MC: "[\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))]"
  sledgehammer [provers = remote_satallax] oops  
  (* by (metis T2 T3 ess_def) *)   text{* Chris: @{text "(metis T2 T3 ess_def)"} still fails on my iMac, will try on my new MacBook tomorrow and then submit. *}
(*<*) 
end
(*>*) 
