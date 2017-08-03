theory BostromPrel
  
  imports BostromMath
    
begin
section "On Formalizing Bostrom\<acute>s \<acute>Simulation Argument\<acute>"
text  {*
In \<acute>Are you living in a Computer Simulation\<acute> and following that \<acute>A Patch for the Simulation Argument\<acute>
Nick Bostrom argues for the disjunctive Thesis that either: \<acute>the human species is very likely to go
extinct before reaching a \<acute>posthuman\<acute> stage\<acute> or \<acute>any posthuman civilization is extremely unlikely 
to run a significant number of simulations of their evolutionary history (or variants thereof)\<acute>
or \<acute>We are almost certainly living in a computer simulation.\<acute>

The argument relies on a couple of metaphysical and normative assumptions. Most importantly the
thesis that the simulated forbears in a simulation of \<acute>their evolutionary history\<acute> (henceforth 
Ancestor simulations) are really conscious (given a fine-grained simulation of their \<acute>brain\<acute> states).

Because Bostrom\<acute>s focus lies on such individuals that are either real or simulated in such a way as
to be conscious we can identify simulations with the sets of individuals that are fine-grained enough
to be (potentially) conscious. If there is no such finely-grained simulated being in a simulation,
we will treat the simulation as the empty set. For real persons we can equally well identify their
societies as sets of (real) individuals. With the exception of the empty set, identity conditions for sets mirror identity conditions for
simulations and (real) civilizations nicely (i.e. they are the same iff they have the same individuals in them).

first lets introduce a type for those beings that have a sufficiently fine-grained neurological processes
i.e. that are real or simulated to great detail. We will call those beings potentially conscious 
because a functionalist will claim that they are conscious whereas other metaphysical positions 
will deny their consciousness.
*}
typedecl b

text {*  
Since Bostrom is only interested in those simulations that have (potentially) conscious beings in them
the empty set doesn\<acute>t pose a problem.

We can state Bostrom\<acute>s metaphysical assumptions that such fine-grained simulated beings are
/in fact/ conscious explicitly. In the next paragraph we will introduce the predicate "being"
for those entities whose consciousness is roughly like our own. We will call those individuals
(simulated or real) "beings".

Another potential problem for modeling simulations and (real) civilizations as sets is that
we can not easily model their evolution over time. The set of people living on earth today is 
disjunct from the set of people that lived 200 years ago, still they are the same civilization 
(if we see humanity as comprising a single civilization).
For this approach to make sense we will have to identify societies (simulated or real) with the
set of all people that have ever (or will ever) been part of it.
There is a clear downside to this as we can not model the /current/ state of our own civilization.
It seems however that in Bostrom\<acute>s natural language argument the same problem arises.
This point will be discussed in more detail below.

Another important thesis is what Bostrom calls the "Bland Indifference Principle". He states it
most clearly in his original paper: "[...]If we knew that a fraction x of all observers with 
human-type experiences [what we called beings above] live in simulations, and we don\<acute>t have any 
information that indicate that our own particular experiences are any more or less likely than
other human-type experiences to have been implemented /in vivo/ rather than /in machina/, then
our credence that we are in a simulation should equal x."

For this principle to be of use we have to have a way to satisfy the two conditions in the 
antecedens. The problem is however that there is (perhaps in principle) no way we could ever 
/know/ this fraction x. Given our current knowledge we don\<acute>t even know if there are any simulated
beings at all.

If this is correct than the Simulation Argument as presented by Bostrom is a non-sequitur. This
poses an extra challenge for a formalization attempt since clearly a non-valid formal argument is
of little use. In this formalization axioms are introduced that correspond somewhat to the
Indifference Principle but make the argument indeed sound. It is not entirely clear whether there
is a reading of these axioms that would repair Bostrom\<acute>s natural language argument.

Lastly, it should be mentioned that there is (at least) one other son-sequitur in Bostrom\<acute>s original
paper. In "A Patch for the Simulation Argument" Bostrom and Kulczycki try to fix this by introducing
new premises. They give two possible "patches" that have (as will be seen in the respective formalization)
 their own problems.
*}
  
  
  text "Depending on how one reads Bostrom, the following is a counterexample:
Suppose that humanity is the only civilization in existence. Suppose further there is a 50% chance
of humanity reaching a posthuman stage. Suppose further that given that humanity reaches that stage,
they will run countless simulations of their evolutionary history."
  

      
text "First we\<acute>ll define a constant for CONSCIOUS  beings whether they are simulated or not"
consts being :: "b \<Rightarrow> bool"  

text "Next we will define a predicate for a being that is posthuman or lives in a posthuman society 
(whether simulated or not)"  
consts posthuman :: "b \<Rightarrow> bool"

text "All those beings that are not posthuman we will call preposthuman"  
abbreviation preposthuman :: "b \<Rightarrow> bool"
  where "preposthuman B \<equiv> \<not> posthuman B" 
    
text "In the following we will identify simulations and (real) civilizations with the sets of potentially conscious beings in them.
This has a couple of hidden assumptions such that no quasi-being is part of two civilizations. But a close
reading of Bostrom shows that for his argument to succeed he needs these assumptions as well."

text "Note that this makes no metaphysical assumptions about either simulations or civilizations.
Some \<acute>simulations\<acute> (e.g. video games) are not sufficiently fine-grained to include any potentially conscious beings, i.e. those
that have fine-grained neural processes, at all.
We can concede this point and simply use the predicate only for those simulations that are
simulations that feature such beings. The fact that we only call something a civilization if
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
simulation has at least one quasi-being in it. I.e. the empty set is not a simulation in our sense."
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
The following Axiom is therefore more or less equivalent to Bostrom\<acute>s substrate independence thesis." 
axiomatization where onlyBeingsInSims: "(B \<in> S \<and> simulation S) \<longrightarrow> being B"  

text "The same goes (without any metaphysical worries) for civilizations"
axiomatization where onlyBeingsInCivs: "(B \<in> C \<and> civilization C) \<longrightarrow> being B"  

text "We also need to make sure the set of real beings and simulated (potentially conscious) beings is disjoint."
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
  
text "We also need that two different societies cannot run the same ancestor simulation."
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