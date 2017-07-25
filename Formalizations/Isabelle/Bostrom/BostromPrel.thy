theory BostromPrel
  
  imports BostromMath
    
begin
  
section "Preliminaries for the Simulation Argument"  
  
text "What we want to focus on is the quantity of simulated beings. Bostrom claims that
there exists a relationship between computational processes in the brain or a computer
ans consciousness (a version of functionalism).
We will therefore introduce a type b that applies only to those things that have those
processes. We will call those things \<acute>Quasi-Beings\<acute>, since it is (for now) an open question
whether they are in fact conscious and deserve the term \<acute>being\<acute>."  
typedecl b (*Term for Quasi-Beings*)
      
text "First we\<acute>ll define a constant for CONSCIOUS  beings whether they are simulated or not"
consts being :: "b \<Rightarrow> bool"  

text "Next we will define a predicate for a being that is posthuman or lives in a posthuman society 
(whether simulated or not)"  
consts posthuman :: "b \<Rightarrow> bool"

text "All those beings that are not posthuman we will call preposthuman"  
abbreviation preposthuman :: "b \<Rightarrow> bool"
  where "preposthuman B \<equiv> \<not> posthuman B" 
    
text "In the following we will identify simulations and (real) civilizations with the sets of quasi-beings in them.
This has a couple of hidden assumptions such that no quasi-being is part of two civilizations. But a close
reading of Bostrom shows that for his argument to succeed he needs these assumptions as well."

text "Note that this makes no metaphysical assumptions about either simulations or civilizations.
Some \<acute>simulations\<acute> (e.g. video games) are not sufficiently fine-grained to include any quasi-beings at all.
We can concede this point and simply use the predicate only for those simulations that are
simulations that feature quasi-beings. The fact that we only call something a civilization if
it contains \<acute>citizens\<acute> should be uncontroversial."  
    
text "We will differentiate between civilizations (non-simulated), ancestor simulations and all simulations,
that satisfy the above condition"
consts civilization :: "b set \<Rightarrow> bool" (*nonsimulated*)
consts ancsimulation:: "b set \<Rightarrow> bool" 
consts simulation :: "b set \<Rightarrow> bool"
  
text "We have to make sure that ancestor simulations are simulations"  
axiomatization where ancsimIsSim:"ancsimulation X \<Longrightarrow> simulation X"

text "Next we define a predicate for the fact that a society (simulated or not) 
runs an ancestor simulation. This predicate is to be interpreted as being False if
either the first argument is no society or the second not a simulation."  
consts SocRunsSim :: "b set \<Rightarrow> b set \<Rightarrow> bool" ("_Runs_")  

text "In the spirit of what it means to be a simulation we want to make sure that each
simulation has at least one quasi-being in it. I.E. the empty set is not a simulation. "
axiomatization where emptNotSim: "simulation S \<Longrightarrow> \<exists>B. B\<in>S"

text "We can now define what it means for something (in our case conscious beings) to be simulated."
abbreviation simulated :: "b \<Rightarrow> bool" 
  where "simulated B \<equiv> \<exists>S. (simulation S \<and> B \<in> S)"  

abbreviation ancsimulated :: "b \<Rightarrow> bool"
  where "ancsimulated B \<equiv> \<exists>S. (ancsimulation S \<and> B \<in> S)"

abbreviation real :: "b \<Rightarrow> bool"
  where "real B \<equiv> \<exists>C. (civilization C \<and> B \<in> C)"
    
text "For the argument we need that every simulated being belongs to one and only one simulation."
axiomatization where everysiminasim: "\<forall>B. (being B \<and> simulated B) \<longrightarrow> (\<exists>S. simulation S \<and> B \<in> S \<and> (\<forall>T. ((simulation T \<and> B \<in> T) \<longrightarrow> (S = T))))"  

text "Next we need the fact that (all) simulated things are in fact conscious beings.
The following Axiom is therefore more or less equivalent to Bostroms substrate independence thesis." 
axiomatization where onlyBeingsInSims: "(B \<in> S \<and> simulation S) \<longrightarrow> being B"  

text "The same goes (without any metaphysical worries) for civilizations"
axiomatization where onlyBeingsInCivs: "(B \<in> C \<and> civilization C) \<longrightarrow> being B"  

text "We also need to make sure the set of real quasi-beings and simulated quasi-beings is disjoint."
axiomatization where diffSimCiv: "real X \<longleftrightarrow> \<not> simulated X"
  
text "Next we need to make sure that the number of simulated people in an ancestor simulation
is equal to the preposthuman population of the simulation." (*N.B.: It is not clear whether this is the correct approach.
Since not all simulations that are running have "gotten to the point" where really all beings
are already simulated*)  

axiomatization where RunsAnc: "(A Runs S) \<Longrightarrow> ancsimulation S"  

axiomatization where prepostinsims: "(A Runs S) \<longrightarrow> (\<exists>M. (M\<subseteq> S) \<and> (\<forall>B\<in>M. (preposthuman B)) \<and> card M = card {B. (being B) \<and> (B \<in> A) \<and> (preposthuman B)})"  
    
text "We also need to make sure that there are no beings that are neither real nor simulated."  
axiomatization where realorsim: "being (x) \<Longrightarrow> ((\<exists>C. (x \<in> C \<and> civilization C)) \<or> (\<exists>S. (simulation S \<and> x \<in> S)))"  
  
text "And we want that we only have a finite number of beings in our universe"  
axiomatization where finiteuniverse: "finite {B. being B}"  

lemma sizeofsims: "(A Runs S) \<longrightarrow> (ancsimulation S \<and> card S \<ge> card {B. (being B) \<and> (B \<in> A) \<and> (preposthuman B)})" 
proof -
  {assume asm: "A Runs S"
    hence cj1: "ancsimulation S" using RunsAnc by simp
    have finS: "finite S" using finiteuniverse  by (metis ancsimIsSim cj1 finite_subset mem_Collect_eq onlyBeingsInSims subsetI)
    from asm prepostinsims have "(\<exists>M. (M\<subseteq> S) \<and> (\<forall>B\<in>M. (preposthuman B)) \<and> card M = card {B. (being B) \<and> (B \<in> A) \<and> (preposthuman B)})" by blast    
    hence "card S \<ge> card {B. (being B) \<and> (B \<in> A) \<and> (preposthuman B)}" using finS by (metis card_mono)
    hence " (ancsimulation S \<and> card S \<ge> card {B. (being B) \<and> (B \<in> A) \<and> (preposthuman B)})" using cj1 by blast}  
 thus ?thesis by blast
qed

axiomatization where citizenship: "\<forall>B. (real B \<longrightarrow> (\<exists>C. ((civilization C \<and> B \<in> C)) \<and> (\<forall>D. ((civilization D \<and> B \<in> D) \<longrightarrow> D = C))))"

lemma citizenship2: "real B \<Longrightarrow> (B \<in> C \<and> civilization C) \<Longrightarrow> (B \<in> D \<and> civilization D) \<Longrightarrow> C = D" using citizenship by auto  
  
text "We also need that two different societies cannot run the same simulation."
axiomatization where DiffVivDiffSim: "(A \<noteq> B) \<Longrightarrow> ((A Runs S) \<and> (B Runs T)) \<Longrightarrow> (S \<inter> T  = {})"

lemma discrSim: "A Runs S \<Longrightarrow> B Runs S \<Longrightarrow> A = B" by (metis DiffVivDiffSim RunsAnc ancsimIsSim emptNotSim emptyE inf.idem)
  
text "We will call a society posthuman iff there is a member in it that is posthuman."  
abbreviation posthumansoc:: "b set \<Rightarrow> bool"
  where "posthumansoc C \<equiv> \<exists>B\<in>C. (posthuman B)"

text "We then postulate that only posthuman societies can run (ancestor) simulations."
axiomatization where OnlyPostSim: "C Runs S \<Longrightarrow> posthumansoc C"    
  
text "One more axiom that makes a couple of proofs a lot more straight forward."
axiomatization where prepostisbeing: "preposthuman x \<Longrightarrow> being x"
  
end  