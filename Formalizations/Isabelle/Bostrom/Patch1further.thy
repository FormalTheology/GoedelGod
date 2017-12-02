theory Patch1further
imports SimArgPatch1


begin
text "Further investigations into the formalization of
Bostrom\<acute>s Simulation Argument using his first patch"

section "Consistency"

lemma True nitpick[user_axioms, satisfy, verbose, timeout = 300]  
  oops
    (*Limit reached: arity 10 of Kodkod relation associated with "Hilbert_Choice.Eps" too large for a
universe of size 10; skipping scope 
Nitpick checked 1 of 100 scopes 
Total time: 153.7 s*)
lemma False sledgehammer[verbose]
  oops
    (*"z3": Timed out 
"cvc4": Timed out 
"spass": Timed out 
"e": Timed out*)
lemma False sledgehammer[remote_leo2 remote_satallax remote_vampire, verbose]
  oops
    (*"remote_leo2": The prover gave up 
"remote_satallax": Timed out 
"remote_vampire": Timed out*)
 
text "Neither consistency nor inconsistency can be proven using Isabelle\<acute>s standard tools"    

section "Unintended consequences"

text "Bostrom\<acute>s additional \<acute>Patch 1\<acute> premise entails the existence of a civilization that runs at least N,
in the case of the argument 9901, ancestor simulations. This is of course something that we could
not possibly know. Note that this is no defect of the formalization but is entailed by Bostrom\<acute>s
natural language premises as well"  
  
lemma LotsOfSims: "\<exists>C. civilization C \<and> (C runs N sims)" using diffex  by (metis (no_types, lifting) card.empty empty_Collect_eq eq_divide_eq of_nat_0)

text "This problem is caused by the fact that Bostrom\<acute>s \<acute>mean population size\<acute> requires that
there are in fact civilizations of which the mean can be taken. Setting this value to 0 if there
are no civilizations makes the argument unsound."    

end