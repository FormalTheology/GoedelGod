theory SimArgPatch1
  
  imports Complex_Main
    
begin
typedecl b (*Things in the world*)
  
  
section "Useful Lemmas for the upcoming proofs"  
   
lemma choiceit: "finite (A:: 'a set set set) \<Longrightarrow> \<forall>S\<in>A. finite S \<Longrightarrow> (\<forall>C \<in> A. (\<forall>D \<in> A. (C \<noteq> D \<longrightarrow> C \<inter> D = {})))
 \<longrightarrow> (C \<in> A \<longrightarrow> S \<in> C \<longrightarrow> T \<in> C \<longrightarrow> C \<noteq> D \<longrightarrow> C \<inter> D = {})
 \<longrightarrow> (\<exists>M. (\<forall>C\<in>A. (\<exists>S\<in>C. (S \<subseteq> M \<and> (\<forall>T\<in>C. (T \<noteq> S \<longrightarrow> T \<inter> M = {}))))))"  
proof -
  {assume asm1: "(\<forall>C \<in> (A:: 'a set set set). (\<forall>D \<in> A. (C \<noteq> D \<longrightarrow> C \<inter> D = {})))" 
oops

lemma relbig: "y \<ge> 0 \<Longrightarrow> z \<ge> 0 \<Longrightarrow> (yy::real) \<ge> y \<Longrightarrow> yy / (yy + z) \<ge> y /(y + z)" 
proof -
  {assume asm1: "y \<ge> 0"
      and asm2: "z \<ge> 0"
      and asm3: "yy \<ge> y"
    {assume "y + z = 0"
      hence "yy / (yy + z) \<ge> y /(y + z)" using asm1 asm2 asm3 by force}
    moreover {assume "y + z \<noteq> 0"
     hence yz: "y + z > 0" using asm1 asm2 by simp   
    {assume "yy = y"
      hence "yy / (yy + z) \<ge> y /(y + z)" by blast}
    moreover 
    {assume "yy \<noteq> y"    
     hence bi: "yy > y" using asm3 by simp   
     hence "\<exists>k. yy = y + k" by algebra
     then obtain k where obtk: "yy = y + k" by auto  
     hence kb0: "k > 0" using bi by force 
     hence "k * z \<ge> 0" using asm2  by force
     hence ine1: "y * y + y * z + y * k + k * z \<ge> y * y + y * z + y * k" by fastforce 
     have "y * y + y * z + y * k + k * z = (y + k) * (y + z)" by algebra 
     hence "(y + k) * (y + z) \<ge> y * y + y * z + y * k" using ine1 by presburger 
     hence "yy * (y + z) \<ge> y * y + y * z + y * k" using obtk by presburger
     hence ine2: "yy * (y + z) \<ge> y * (y + k + z)" by argo (*slow*)    
     from yz have "(1/ (y + z)) > 0" by simp
     hence "yy * (y + z) * (1/ (y + z)) \<ge> y * (y + k + z) * (1/ (y + z))" using ine2 real_mult_le_cancel_iff1 by presburger  
     hence ine3: "yy  \<ge> y * (y + k + z) /(y + z)" using yz by simp  
     from yz kb0 have yyz: "1 / (y + k + z) > 0" by simp 
     hence "yy *(1 / (y + k + z))  \<ge>  y * (y + k + z) /(y + z) * (1 / (y + k + z))" using ine3 real_mult_le_cancel_iff1 by presburger 
     hence "yy / (y + k + z)  \<ge>  y / (y + z)" using yyz by simp
     hence "yy / (yy + z) \<ge> y / (y + z)" using obtk by simp}    
   ultimately have "yy / (yy + z) \<ge> y /(y + z)" by blast}
  ultimately have "yy / (yy + z) \<ge> y /(y + z)" by blast}
thus "y \<ge> 0 \<Longrightarrow> z \<ge> 0 \<Longrightarrow> (yy::real) \<ge> y \<Longrightarrow> yy / (yy + z) \<ge> y /(y + z)"  by simp  
qed         

lemma relsmall: "yy \<ge> 0 \<Longrightarrow> z \<ge> 0 \<Longrightarrow> (yy::real) \<le> y \<Longrightarrow> yy / (yy + z) \<le> y /(y + z)" using relbig by meson

lemma bigfinite: "finite (U::'a set set) \<Longrightarrow> (\<And>T. T \<in> U \<Longrightarrow> finite T) \<Longrightarrow> finite (\<Union>U)" by auto  

lemma meancard: 
assumes a1: "finite (U:: 'a set set)"  
and a2: "\<forall>S\<in>U. finite S"
and a3: "\<forall>S T. (S \<noteq> T) \<longrightarrow> (S \<in> U) \<longrightarrow> (T \<in> U) \<longrightarrow>  (S \<inter> T = {})"
and a4: "\<forall>S\<in>U. (S \<noteq>{})"
shows "card (\<Union>U) = (card U) * (card {B. \<exists>S\<in>U. (B \<in> S)}) / card U"
proof -
  have "card U = 0 \<or> card U > 0" by auto
  moreover 
  {assume "card U = 0"
    hence "U = {}" using a1 by simp
    hence "card (\<Union>U) = (card U) * (card {B. \<exists>S\<in>U. (B \<in> S)}) / card U" by fastforce}    
  moreover 
  {assume "card U > 0"
    hence alg1: "(card U) * (card {B. \<exists>S\<in>U. (B \<in> S)}) / card U = card {B. \<exists>S\<in>U. (B \<in> S)}" by force
    from a1 a2 a3 a4 have "card (\<Union>U) = card {B. \<exists>S\<in>U. (B \<in> S)}" by (metis Union_eq)
    hence "card (\<Union>U) = (card U) * (card {B. \<exists>S\<in>U. (B \<in> S)}) / card U" using alg1 by presburger}
  ultimately show ?thesis by linarith
qed      
  
lemma bigunionmult: "\<And>U. (card (U::'a set set) \<ge> p \<Longrightarrow>
  (\<And>S. S \<in> U \<Longrightarrow> (card S \<ge> q)) \<Longrightarrow> (\<And>S. S \<in> U \<Longrightarrow> (finite S)) \<Longrightarrow>
(\<And>S T. (S \<in> U \<Longrightarrow> T \<in> U \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {})) \<Longrightarrow> card (\<Union>U) \<ge> p * q)"
  proof (induct p)
    case 0
    then show ?case using card_eq_0_iff card_empty  finite_UnionD by linarith 
  next
    case (Suc p)
    from Suc.prems have cd: "card U \<ge> Suc p" by simp
    hence "U \<noteq> {}" by auto
    hence "\<exists>S. S  \<in> U" by auto
    then obtain S where obtS: "S \<in> U" by auto
    let ?nU = "U - {S}"
    from obtS cd have "card (?nU) \<ge> p" by (simp add: card_Diff_subset)
    hence cd2: "card (\<Union>?nU) \<ge> p * q" using Suc.prems Suc.hyps using Diff_subset by fastforce  
    from Suc.prems obtS have inter1: "(S \<inter> (\<Union>?nU)) = {}" by blast
    from Suc.prems obtS have finS: "finite S" by blast  
    from cd have "card U > 0" by fastforce
    hence "finite U" using card_ge_0_finite by auto    
    hence "finite (\<Union>U)" using Suc.prems bigfinite by blast
    hence "finite (\<Union>?nU)" using Suc.prems(3) \<open>finite U\<close> by auto    
    hence "card (S \<union> (\<Union>?nU)) = card S + card (\<Union>?nU)" using inter1 finS  card_Un_disjoint by metis   
    hence "card (\<Union>U) = card S + card (\<Union>?nU)" using obtS Suc.prems by (metis Sup_insert insert_Diff)
    hence "card (\<Union>U) \<ge> card S + (p * q)" using cd2 by force
    hence "card (\<Union>U) \<ge> q + (p * q)" using Suc.prems obtS by fastforce
    then show ?case by fastforce
qed

lemma bigunionmult2: "\<And>U. (card (U::'a set set) \<ge> p \<Longrightarrow>
  (\<And>S. S \<in> U \<Longrightarrow> (card (S \<inter> CS) \<ge> q)) \<Longrightarrow> (\<And>S. S \<in> U \<Longrightarrow> (finite S)) \<Longrightarrow>
(\<And>S T. (S \<in> U \<Longrightarrow> T \<in> U \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {})) \<Longrightarrow> card (\<Union>U \<inter> CS) \<ge> p * q)"
  proof (induct p)
    case 0
    then show ?case using card_eq_0_iff card_empty  finite_UnionD by linarith 
  next
    case (Suc p)
    from Suc.prems have cd: "card U \<ge> Suc p" by simp
    hence "U \<noteq> {}" by auto
    hence "\<exists>S. S  \<in> U" by auto
    then obtain S where obtS: "S \<in> U" by auto
    let ?nU = "U - {S}"
    from obtS cd have "card ?nU \<ge> p" by (simp add: card_Diff_subset)
    hence cd2: "card (\<Union>?nU \<inter> CS) \<ge> p * q" using Suc.prems Suc.hyps using Diff_subset by fastforce  
    from Suc.prems obtS have inter1: "((S \<inter> CS) \<inter> (\<Union>?nU \<inter> CS)) = {}" by blast
    from Suc.prems obtS have finS: "finite (S \<inter> CS)" by blast    
    from cd have "card U > 0" by fastforce
    hence "finite U" using card_ge_0_finite by auto    
    hence "finite (\<Union>U)" using Suc.prems bigfinite by blast
    hence "finite (\<Union>?nU \<inter> CS)" using Suc.prems(3) \<open>finite U\<close> by auto    
    hence "card ((S \<inter> CS) \<union> (\<Union>?nU \<inter> CS)) = card (S \<inter> CS) + card (\<Union>?nU \<inter> CS)" using inter1 finS  card_Un_disjoint by metis
    hence "card (\<Union>U \<inter> CS) = card (S \<inter> CS) + card (\<Union>?nU \<inter> CS)" using obtS Suc.prems Sup_insert insert_Diff by (metis Int_Un_distrib2)
    hence "card (\<Union>U \<inter> CS) \<ge> card (S \<inter> CS) + (p * q)" using cd2 by force
    hence "card (\<Union>U \<inter> CS) \<ge> q + (p * q)" using Suc.prems obtS by fastforce
    then show ?case by fastforce
qed  
  
    
section "Preliminaries for the formalization of Bostrom\<acute>s Appendix"    
    
text "First we\<acute>ll define a constant for conscious beings whether they are simulated or not"
consts being :: "b \<Rightarrow> bool"  

text "Next we will define a predicate for a being that is posthuman or lives in a posthuman society 
(whether simulated or not)"  
consts posthuman :: "b \<Rightarrow> bool"

text "All those beings that are not posthuman we will call preposthuman"  
abbreviation preposthuman :: "b \<Rightarrow> bool"
  where "preposthuman B \<equiv> \<not> posthuman B" 
    
text "In the following we will identify simulations and civilizations with the sets of beings in it.
This has a couple of hidden assumptions such that no being is part of two civilizations. But a close
reading of Bostrom shows that for his argument to succeed he needs these assumptions as well."

text "We will differentiate between civilizations (non-simulated), ancestor simulations and all simulations."
consts civilization :: "b set \<Rightarrow> bool" (*nonsimulated*)
consts ancsimulation:: "b set \<Rightarrow> bool" 
consts simulation :: "b set \<Rightarrow> bool"
  
text "We have to make sure that ancestor simulations are simulations"  
axiomatization where ancsimIsSim:"ancsimulation X \<Longrightarrow> simulation X"

text "Next we define a predicate for the fact that a society (simulated or not) runs a ancestor simulation"  
consts CivRunsSim :: "b set \<Rightarrow> b set \<Rightarrow> bool" ("_Runs_")  

text "We want to make sure that no to societies run the same simulation."
axiomatization where discrSim: "A Runs S \<Longrightarrow> B Runs S \<Longrightarrow> A = B"
  (*A weaker version of this namely A Runs S \<Longrightarrow> B Runs S \<Longrightarrow> (A = B \<or> S = {}) follows
already from the other axioms.*)
  
text "For Bostrom\<acute>s argument it is also useful to define a predicate for the fact that a society
runs at least N different ancestor simulations."  
abbreviation RunsNsims :: "b set \<Rightarrow> nat \<Rightarrow> bool" ("_ runs _ sims")
  where "C runs N sims \<equiv> card {S. (C Runs S)} \<ge> N"

text "We can no define what it means for something (in our case conscious beings) to be simulated."
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

text "We also need to make sure that no simulation is a civilization and vice versa" (*word this better?*)
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
  (* Ignore these for now.
axiomatization where civreal: "(\<forall>B. (\<exists> C. (B::b) \<in> C \<and> civilization C) \<longleftrightarrow> real B)"
axiomatization where civnotempt: "civilization S \<Longrightarrow> (\<exists>b. (being b \<and> b \<in> S))"  
*)
axiomatization where citizenship: "\<forall>B. (real B \<longrightarrow> (\<exists>C. ((civilization C \<and> B \<in> C)) \<and> (\<forall>D. ((civilization D \<and> B \<in> D) \<longrightarrow> D = C))))"

lemma citizenship2: "real B \<Longrightarrow> (B \<in> C \<and> civilization C) \<Longrightarrow> (B \<in> D \<and> civilization D) \<Longrightarrow> C = D" using citizenship by auto  
  
text "Let N be a very large number such that there have been s civilizations 
that have run at least N ancestor simulations each"   
consts N::nat       
axiomatization where prettybig: "N > 0"  

text "We also need that two different societies cannot run the same simulation."
axiomatization where DiffVivDiffSim: "(A \<noteq> B) \<Longrightarrow> ((A Runs S) \<and> (B Runs T)) \<Longrightarrow> (S \<inter> T  = {})"

text "We will call a society posthuman iff there is a member in it that is posthuman."  
abbreviation posthumansoc:: "b set \<Rightarrow> bool"
  where "posthumansoc C \<equiv> \<exists>B\<in>C. (posthuman B)"
text "We then postulate that only posthuman societies can run (ancestor) simulations."
axiomatization where OnlyPostSim: "C Runs S \<Longrightarrow> posthumansoc C"  
  
  
text "One more axiom that makes a couple of proofs a lot more straight forward."
  axiomatization where prepostisbeing: "preposthuman x \<Longrightarrow> being x"
  (* ignore this
axiomatization where NumAndSizeOfSims: "(A runs (K::nat) sims) \<Longrightarrow> (\<exists>Se. (\<forall>S \<in> Se.  (A Runs S))  \<and> (card Se = K))"  
*)
  
abbreviation s :: "nat"
  where "s \<equiv> card {C. civilization C \<and> (C runs N sims)}"

text "Let H_s be the average number of pre-posthuman beings in those civilizations"  
abbreviation H\<^sub>s :: "real"
 where "H\<^sub>s \<equiv> ((card {B. being B \<and>  preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}) / s)"
                                   
text "let n be the number of civilizations that have run fewer than N ancestor simulations"
abbreviation n :: "nat"
  where "n \<equiv> card ({C. civilization C} - {C. C runs N sims})"    
  
text "let H_n be the average number of pre-posthuman beings in those civilizations"
abbreviation H\<^sub>n :: "real"
 where "H\<^sub>n \<equiv> ((card {B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> (C runs N sims))))}) / n)"
  
axiomatization where quot: "(H\<^sub>n / H\<^sub>s) \<le> (N / 1000000)"   
axiomatization where diffex: "H\<^sub>n/H\<^sub>s \<noteq> 0" (*Perhaps use this as an assumption*)

section "Formalization of the mathematical elements of the Simulation Argument with the first Patch"  
  
  
lemma "{B. simulated B} \<supseteq> {B. ancsimulated B}" using ancsimIsSim by auto
lemma "{B. ancsimulated B} \<supseteq> {B. \<exists>S. B \<in> S \<and>  (\<exists>C. (C Runs S) \<and> (C runs N sims))}"  using sizeofsims by force 

lemma simsize2: "C Runs S \<Longrightarrow> card S \<ge> card {B. being B \<and>  preposthuman B \<and> B \<in> C}"  by (metis (no_types, lifting) Collect_cong sizeofsims)
    
lemma allbeings: "card {B. being B \<and> preposthuman B \<and> real B} = s * H\<^sub>s + n * H\<^sub>n"
proof -
 have "{B. being B \<and> preposthuman B \<and> real B} = {B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C))}"  by auto 
 hence "{B. being B \<and> preposthuman B \<and> real B} = {B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> ((C runs N sims) \<or> (\<not> C runs N sims))))}" by force
 hence a: "{B. being B \<and> preposthuman B \<and> real B} = ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}) \<union> ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> C runs N sims)))})" by auto
 have fin1: "finite ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> C runs N sims)))})" using finiteuniverse by fast  
 have fin2: "finite ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))})" using finiteuniverse by fast  
  have dist1: "({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}) \<inter> ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> C runs N sims)))}) = {}"
  proof -
    {assume "({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}) \<inter> ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> C runs N sims)))}) \<noteq> {}"
      hence "\<exists>B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims))) \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> C runs N sims)))" by blast
      then obtain B where obtB: "being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims))) \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> C runs N sims)))" by auto   
      then obtain C D where obtBC: "(B \<in> C \<and> civilization C \<and> (C runs N sims)) \<and> (B \<in> D \<and> civilization D \<and> (\<not> D runs N sims))" by auto
      hence "C = D" using obtB by (metis citizenship subsetI subset_antisym)
      hence "(C runs N sims) \<and> \<not> (C runs N sims)" using obtBC by auto
      hence False by blast}
    thus ?thesis by presburger qed
  hence sum: "card {B. being B \<and> preposthuman B \<and> real B} =  card ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}) +  card ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> C runs N sims)))})"
  using fin1 fin2 a card_Un_disjoint by force
  hence s1: "card ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}) = H\<^sub>s * s" using diffex by force 
  hence s2: "card ({B. being B \<and> preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (\<not> C runs N sims)))}) = H\<^sub>n * n" using diffex by force
  then show ?thesis using s1 sum by (metis (mono_tags, lifting) mult_of_nat_commute of_nat_add)
qed    
   
  
lemma simineqhelper1: "C \<noteq> D \<Longrightarrow> {B. being B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))} \<inter> {B. being B \<and> (\<exists>S. ((D Runs S) \<and> B \<in> S))} = {}"
proof -
{assume CnotD: "C \<noteq> D"  
  {assume red: "\<exists>B. B \<in> {B. being B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))} \<and> B \<in> {B. being B \<and> (\<exists>S. ((D Runs S) \<and> B \<in> S))}"
    then obtain B where obtB: " B \<in> {B. being B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))} \<and> B \<in> {B. being B \<and> (\<exists>S. ((D Runs S) \<and> B \<in> S))}" by auto
    hence "\<exists>S. ((C Runs S) \<and> B \<in> S)" by simp
    then obtain S where obtS: "(C Runs S) \<and> B \<in> S" by auto
    from obtB have "\<exists>T. ((D Runs T) \<and> B \<in> T)" by auto
    then obtain T where obtT: "(D Runs T) \<and> B \<in> T" by auto   
    from CnotD obtT obtS have "T \<inter> S = {}" using DiffVivDiffSim by blast
    hence False using obtS obtT by auto}
  hence " {B. being B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))} \<inter> {B. being B \<and> (\<exists>S. ((D Runs S) \<and> B \<in> S))} = {}" by blast}
  thus  "C \<noteq> D \<Longrightarrow> {B. being B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))} \<inter> {B. being B \<and> (\<exists>S. ((D Runs S) \<and> B \<in> S))} = {}" by argo
qed
  

  
lemma simineqhelper2: "(C runs N sims) \<Longrightarrow> card {B. being B \<and> preposthuman B \<and> (\<exists>S. ( (C Runs S) \<and> B \<in> S))} \<ge> N *  card {B. being B \<and>  preposthuman B \<and> B \<in> C}"
proof -
  let ?CS = "{B. preposthuman B}"
  {assume bigsim: "C runs N sims"
  hence ca1: "card {S. (C Runs S)} \<ge> N" by blast
  have ca2: "\<forall>S. (S \<in> {T. C Runs T} \<longrightarrow> card (S \<inter> ?CS) \<ge> card {B. being B \<and>  preposthuman B \<and> B \<in> C})"
  proof -
    let ?CS = "{B. preposthuman B}"
    {fix S
     {assume "S \<in> {T. C Runs T}"
      hence th: "C Runs S" by auto  
      hence "(\<exists>M. (M\<subseteq> S) \<and> (\<forall>B\<in>M. (preposthuman B)) \<and> card M = card {B. (being B) \<and> (B \<in> C) \<and> (preposthuman B)})" using prepostinsims by blast
      then obtain M where obtM: "(M\<subseteq> S) \<and> (\<forall>B\<in>M. (preposthuman B)) \<and> card M = card {B. (being B) \<and> (B \<in> C) \<and> (preposthuman B)}" by auto   
      from th have "ancsimulation S" using RunsAnc by auto
      hence fin1: "finite S" using finiteuniverse  by (metis ancsimIsSim finite_subset mem_Collect_eq onlyBeingsInSims subsetI)
      hence fin2: "finite (S \<inter> {B. preposthuman B})" by simp
      have "M \<subseteq> (S \<inter> {B. preposthuman B})" using obtM by blast
      hence "card M \<le> card (S \<inter> {B. preposthuman B})" using fin2 obtM card_mono by blast
      hence stupid1: "card {B. (being B) \<and> (B \<in> C) \<and> (preposthuman B)} \<le> card (S \<inter> {B. preposthuman B})" using obtM by argo
      have "{B. (being B) \<and> (B \<in> C) \<and> (preposthuman B)} =  {B. being B \<and>  preposthuman B \<and> B \<in> C}" by auto
      hence  "card (S \<inter> {B. preposthuman B}) \<ge> card {B. being B \<and>  preposthuman B \<and> B \<in> C}" using stupid1 by argo
      hence "card (S \<inter> {B. preposthuman B}) \<ge> card {B. being B \<and>  preposthuman B \<and> B \<in> C}" by blast} 
    hence "(S \<in> {T. C Runs T} \<Longrightarrow> card (S \<inter> {B. preposthuman B}) \<ge> card {B. being B \<and>  preposthuman B \<and> B \<in> C})" by blast}
    thus ?thesis by blast qed 
  have fins: "(\<And>S. S \<in> {T. C Runs T} \<Longrightarrow> (finite S))" using finiteuniverse by (metis ancsimIsSim mem_Collect_eq onlyBeingsInSims rev_finite_subset sizeofsims subsetI)
  have inter: "(\<And>S T. (S \<in> {X. C Runs X} \<Longrightarrow> T \<in> {X. C Runs X} \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {}))" by (metis (no_types, lifting) ancsimIsSim disjoint_iff_not_equal everysiminasim mem_Collect_eq onlyBeingsInSims sizeofsims)
  hence cardone: "card (\<Union>{T. C Runs T} \<inter> ?CS) \<ge> N * card {B. being B \<and>  preposthuman B \<and> B \<in> C}" using ca1 ca2 fins bigunionmult2 by force (*very slow*)
  have "{B. being B \<and> preposthuman B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))}  = {B. preposthuman B} \<inter> \<Union>{S. (C Runs S)}"
  proof -
    have lr: "{B. being B \<and> preposthuman B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))}  \<subseteq> {B. preposthuman B} \<inter> \<Union>{S. (C Runs S)}"
    proof -
      {fix B
        assume asm: "B \<in> {B. being B \<and> preposthuman B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))}"
        hence "\<exists>S. ((C Runs S) \<and> B \<in> S)" by blast
        then obtain S where obtS: "(C Runs S) \<and> B \<in> S" by auto
        hence "B \<in> (\<Union>{S. (C Runs S)})" by blast
        hence "B \<in>  {B. preposthuman B} \<inter> \<Union>{S. (C Runs S)}" using asm by simp}
      thus ?thesis by auto qed
    have  "{B. being B \<and> preposthuman B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))} \<supseteq> {B. preposthuman B} \<inter> \<Union>{S. (C Runs S)}"
    proof -
      {fix B
        assume "B \<in> {B. preposthuman B} \<inter> \<Union>{S. (C Runs S)}"
        hence "\<exists>S. (C Runs S) \<and> B \<in> S" by simp
        then obtain S where obtS: "(C Runs S) \<and> B \<in> S" by auto
        hence "simulation S \<and> B \<in> S" using ancsimIsSim sizeofsims by blast
        hence "being B" using onlyBeingsInSims by blast
        hence "being B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))" using obtS by fast
        hence "B \<in> {B. being B \<and> (\<exists>S. ((C Runs S) \<and> B \<in> S))}" by simp}
      thus ?thesis by fast qed
    thus ?thesis using lr by fastforce qed
  hence stupid2: "card {B. being B \<and> preposthuman B \<and> (\<exists>S. (C Runs S) \<and> B \<in> S)} = card ({B. preposthuman B} \<inter> \<Union>{S. (C Runs S)})" by presburger  
  have "({B. preposthuman B} \<inter> \<Union>{S. (C Runs S)}) =  (\<Union>{T. C Runs T} \<inter> ?CS)" by fast  
  hence "card ({B. preposthuman B} \<inter> \<Union>{S. (C Runs S)}) = card (\<Union>{T. C Runs T} \<inter> ?CS)" by presburger
  hence "card {B. being B \<and> preposthuman B \<and> (\<exists>S. ( (C Runs S) \<and> B \<in> S))} \<ge> N *  card {B. being B \<and>  preposthuman B \<and> B \<in> C}" using cardone stupid2 by presburger}
  thus "(C runs N sims) \<Longrightarrow> card {B. being B \<and> preposthuman B \<and> (\<exists>S. ( (C Runs S) \<and> B \<in> S))} \<ge> N *  card {B. being B \<and>  preposthuman B \<and> B \<in> C}" by blast
qed      

   
  
lemma simineqhelper25:
"\<And>S1. finite S1 (*{C. RNS C}*)
\<Longrightarrow> \<forall>C. finite {S. (RUNS C S)}
\<Longrightarrow> \<forall>C. C \<in> S1 \<longrightarrow> {S. RUNS C S} \<noteq> {}
\<Longrightarrow> card S1 = k
\<Longrightarrow> card {simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}} = card S1
\<Longrightarrow> \<forall>C. C \<in> S1 \<longrightarrow> card  ({B. preposthuman B} \<inter> (\<Union>{S. (RUNS C S)})) \<ge> N * card {B. B\<in>C \<and> preposthuman B}
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> S1 \<longrightarrow> D \<in> S1 \<longrightarrow> (C \<inter> D) = {})
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> {simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}} \<longrightarrow> D \<in> {simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}} \<longrightarrow> (C \<inter> D) = {} )
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> \<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}} \<longrightarrow> D \<in> \<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}} \<longrightarrow> (C \<inter> D) = {})
\<Longrightarrow> \<forall>C D. C \<noteq> D \<longrightarrow> C \<in> S1 \<longrightarrow> D \<in> S1 \<longrightarrow> {S. (RUNS C S)} \<inter> {S. (RUNS D S)} = {}
\<Longrightarrow> \<forall>C\<in>S1. finite C
\<Longrightarrow> card {B. preposthuman B \<and> B\<in>(\<Union>S1)} * N \<le> card ( {B. preposthuman B} \<inter>(\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}})))" 
proof (induct k)
  case 0
  then show ?case by fastforce                                                 
next
  case (Suc k)
  from Suc.prems have "S1 \<noteq> {}" by force
  hence "\<exists>C. C \<in> S1" by blast
  then obtain C where obtC: "C \<in> S1" by auto
  let ?CRS = "{S. RUNS C S}"  
  let ?othcivs = "S1 - {C}"
  let ?sims = "{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}"
have indhyp: "card {B. preposthuman B \<and> B \<in> \<Union>?othcivs}* N \<le> card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}})))"    
proof -
  have one: "finite ?othcivs" using Suc.prems by blast
  have one2: "\<forall>C. finite {S. (RUNS C S)}" using Suc.prems by simp
  have two: "\<forall>C. C \<in> ?othcivs \<longrightarrow> {S. RUNS C S} \<noteq> {}" using Suc.prems by blast
  have three: "card ?othcivs = k"
  proof - 
    have a: "finite {C}" by simp
    have b: "finite ?othcivs" using Suc.prems by fast
    have c: "{C} \<union> ?othcivs = S1" using obtC by fast
    have d: "{C} \<inter> ?othcivs = {}" using obtC by blast
    from a b d have "card ({C} \<union> ?othcivs) = card {C} + card ?othcivs" using card_Un_disjoint by metis (*slow*) 
    hence "card ({C} \<union> ?othcivs) = 1 + card ?othcivs" by force
    hence "Suc k = 1 + card ?othcivs" using Suc.prems c by argo
    thus ?thesis by force qed
  have three2: " card {simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}} = card ?othcivs"
  proof - 
    have a: "{{S. RUNS C S}} \<union> ?sims = {simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}" using obtC by blast
    have b: "{{S. RUNS C S}} \<inter> ?sims = {}"
    proof - 
      {assume "\<exists>x. x \<in> {{S. RUNS C S}} \<and> x \<in> ?sims"
        hence "{S. RUNS C S} \<in> ?sims" by blast
        hence "\<exists>D\<in>?othcivs. {S. RUNS D S} = {S. RUNS C S}" by auto
        then obtain D where obtD: "D\<in>?othcivs \<and> {S. RUNS D S} = {S. RUNS C S}" by auto
        hence aa: "C \<noteq> D" using obtC by blast                                                    
        hence "{S. RUNS D S} \<inter> {S. RUNS C S} = {}" using Suc.prems obtC obtD
        proof - 
          from Suc.prems have "C \<noteq> D \<longrightarrow> C \<in> S1 \<longrightarrow> D \<in> S1 \<longrightarrow> {S. (RUNS C S)} \<inter> {S. (RUNS D S)} = {}" by presburger (*slow*)
          thus ?thesis using aa obtC obtD by blast qed
        hence False using Suc.prems aa obtC obtD by auto (*slow*)}
       thus ?thesis by auto qed 
    have c: "finite {{S. RUNS C S}}" by simp
    have d: "finite ?sims" using Suc.prems by simp
    from b c d have "card ({{S. RUNS C S}} \<union> ?sims) = card {{S. RUNS C S}} + card ?sims" using card_Un_disjoint by force
    hence "card ({{S. RUNS C S}} \<union> ?sims) = 1 + card ?sims" by fastforce
    hence "card {simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}= 1 + card ?sims" using a by argo
    hence "Suc k = 1 + card ?sims" using Suc.prems by argo
    hence "card ?sims = k" by linarith
    thus ?thesis using three by argo qed
  have four: "\<forall>C. C \<in> ?othcivs \<longrightarrow> card ({B. preposthuman B} \<inter> (\<Union>{S. (RUNS C S)})) \<ge> N * card {B. B\<in>C \<and> preposthuman B}" using Suc.prems by blast   
  have five: "\<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> ?othcivs \<longrightarrow> D \<in> ?othcivs \<longrightarrow> (C \<inter> D) = {})" using Suc.prems by auto
  have six: "\<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> {simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}} \<longrightarrow> D \<in> {simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}} \<longrightarrow> (C \<inter> D) = {})"
  proof -
    { fix BB :: "b set set" and BBa :: "b set set"
      obtain BBb :: "b set set \<Rightarrow> b set" where
        ff1: "\<And>B. ((\<forall>Ba. Ba \<notin> S1 - {C} \<or> B \<noteq> Collect (RUNS Ba)) \<or> Collect (RUNS (BBb B)) = B) \<and> ((\<forall>Ba. Ba \<notin> S1 - {C} \<or> B \<noteq> Collect (RUNS Ba)) \<or> BBb B \<in> S1 - {C})"
        by moura (* 359 ms *)
      then have ff2: "\<And>B. (\<forall>Ba. Ba \<notin> S1 - {C} \<or> B \<noteq> Collect (RUNS Ba)) \<or> BBb B \<in> S1"
        by blast (* 0.0 ms *)
      moreover
      { assume "BBb BB \<in> S1"
        moreover
        { assume "BBb BBa \<in> S1 \<and> BBb BB \<in> S1"
          then have "Collect (RUNS (BBb BBa)) = BBa \<longrightarrow> BBb BB \<in> S1 \<and> (\<exists>B. B \<in> S1 \<and> BBa = Collect (RUNS B))"
            by blast (* 0.0 ms *)
          moreover
          { assume "Collect (RUNS (BBb BBa)) \<noteq> BBa"
            then have "\<forall>B. B \<notin> S1 - {C} \<or> BBa \<noteq> Collect (RUNS B)"
              using ff1 by metis (* 46 ms *) }
          moreover
          { assume "BBb BB \<in> S1 \<and> (\<exists>B. B \<in> S1 \<and> BBa = Collect (RUNS B))"
            moreover
            { assume "Collect (RUNS (BBb BB)) \<noteq> BB"
              then have "\<forall>B. B \<notin> S1 - {C} \<or> BB \<noteq> Collect (RUNS B)"
                using ff1 by metis (* 31 ms *) }
            moreover
            { assume "(\<exists>B. B \<in> S1 \<and> BBa = Collect (RUNS B)) \<and> (\<exists>B. B \<in> S1 \<and> BB = Collect (RUNS B))"
              then have "BBa \<in> {B. \<exists>Ba. Ba \<in> S1 \<and> B = Collect (RUNS Ba)} \<and> BB \<in> {B. \<exists>Ba. Ba \<in> S1 \<and> B = Collect (RUNS Ba)}"
                by auto (* 0.0 ms *)
              moreover
              { assume "BB \<in> {B. \<exists>Ba. Ba \<in> S1 \<and> B = Collect (RUNS Ba)} \<and> BBa \<in> {B. \<exists>Ba. Ba \<in> S1 \<and> B = Collect (RUNS Ba)} \<and> BB \<noteq> BBa"
                then have "BB = BBa \<or> BB \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BBa \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BB \<inter> BBa = {}"       by (metis Suc.prems(10) \<open>(\<exists>B. B \<in> S1 \<and> BBa = Collect (RUNS B)) \<and> (\<exists>B. B \<in> S1 \<and> BB = Collect (RUNS B))\<close>)
              (* > 1.0 s, timed out *) }
              ultimately have "BB = BBa \<or> BB \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BBa \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BB \<inter> BBa = {}"
                by satx (* 0.0 ms *) }
            ultimately have "(BB = BBa \<or> BB \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BBa \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BB \<inter> BBa = {}) \<or> (\<forall>B. B \<notin> S1 - {C} \<or> BB \<noteq> Collect (RUNS B))"
              by metis (* 375 ms *) }
          ultimately have "(BB = BBa \<or> BB \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BBa \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BB \<inter> BBa = {}) \<or> (\<forall>B. B \<notin> S1 - {C} \<or> BB \<noteq> Collect (RUNS B)) \<or> (\<forall>B. B \<notin> S1 - {C} \<or> BBa \<noteq> Collect (RUNS B))"
            by satx (* 62 ms *) }
        moreover
        { assume "BBb BBa \<notin> S1"
          then have "\<forall>B. B \<notin> S1 - {C} \<or> BBa \<noteq> Collect (RUNS B)"
            using ff2 by metis (* 15 ms *) }
        moreover
        { assume "\<forall>B. B \<notin> S1 - {C} \<or> BBa \<noteq> Collect (RUNS B)"
          then have "BB = BBa \<or> BB \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BBa \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BB \<inter> BBa = {}"
            by auto (* 0.0 ms *) }
        ultimately have "(BB = BBa \<or> BB \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BBa \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BB \<inter> BBa = {}) \<or> (\<forall>B. B \<notin> S1 - {C} \<or> BB \<noteq> Collect (RUNS B))"
          by satx (* 62 ms *) }
      moreover
      { assume "\<forall>B. B \<notin> S1 - {C} \<or> BB \<noteq> Collect (RUNS B)"
        then have "BB = BBa \<or> BB \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BBa \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BB \<inter> BBa = {}"
          by auto (* 0.0 ms *) }
      ultimately have "BB = BBa \<or> BB \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BBa \<notin> {B. \<exists>Ba. Ba \<in> S1 - {C} \<and> B = Collect (RUNS Ba)} \<or> BB \<inter> BBa = {}"
        by meson (* 187 ms *) }
    then show ?thesis
      by meson (* 0.0 ms *)
  qed
    have seven: "\<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> \<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}} \<longrightarrow> D \<in> \<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}} \<longrightarrow> (C \<inter> D) = {})"
  proof -
    {fix C D
      assume a: "C \<noteq> D"
      and b: "C \<in> \<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}"
      and c: "D \<in> \<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}"
      from b have bb: "C \<in> \<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}" by blast
      from c have cc: "D \<in> \<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}" by blast
      from a bb cc have "C \<inter> D = {}" using Suc.prems by presburger}
      thus ?thesis by argo qed
    have eight: "\<forall>C D. C \<noteq> D \<longrightarrow> C \<in> ?othcivs \<longrightarrow> D \<in> ?othcivs \<longrightarrow> {S. (RUNS C S)} \<inter> {S. (RUNS D S)} = {}" using Suc.prems by simp
    have ten: "\<forall>C\<in>S1. finite C" using Suc.prems by simp
    thus ?thesis using Suc.hyps ten one one2 two three three2 four five six seven eight inf.idem by blast (*slow*) qed
have lseq: "card {B. preposthuman B \<and> B \<in> \<Union>S1} * N = (card {B. preposthuman B \<and> B \<in> \<Union>?othcivs} + card {B. preposthuman B \<and> B \<in> C}) * N"    
proof -
  have a: "card {B. preposthuman B \<and> B \<in> \<Union>S1} = card {B. preposthuman B \<and> B \<in> \<Union>?othcivs} + card {B. preposthuman B \<and> B \<in> C}"
  proof - 
    have inter: "{B. preposthuman B \<and> B \<in> \<Union>?othcivs} \<inter> {B. preposthuman B \<and> B \<in> C} = {}" using obtC Suc.prems by blast
    have fin1: "finite {B. preposthuman B \<and> B \<in> \<Union>?othcivs}" using Suc.prems obtC by force
    have fin2: "finite {B. preposthuman B \<and> B \<in> C}" using Suc.prems obtC by force
    hence caa: "card ({B. preposthuman B \<and> B \<in> \<Union>?othcivs} \<union> {B. preposthuman B \<and> B \<in> C}) = card {B. preposthuman B \<and> B \<in> \<Union>?othcivs} + card {B. preposthuman B \<and> B \<in> C}" using fin1 inter card_Un_disjoint by blast  
    have "{B. preposthuman B \<and> B \<in> \<Union>?othcivs} \<union> {B. preposthuman B \<and> B \<in> C} =  {B. preposthuman B \<and> B \<in> \<Union>S1}" using obtC by auto
    hence  "card ({B. preposthuman B \<and> B \<in> \<Union>?othcivs} \<union> {B. preposthuman B \<and> B \<in> C}) =  card {B. preposthuman B \<and> B \<in> \<Union>S1}" using obtC by auto
    thus ?thesis using caa by argo qed    
  thus ?thesis by argo qed
hence "card {B. preposthuman B \<and> B \<in> \<Union>S1} * N = (card {B. preposthuman B \<and> B \<in> \<Union>?othcivs} * N) + (card {B. preposthuman B \<and> B \<in> C} * N)" by algebra
  hence sf2: "card {B. preposthuman B \<and> B \<in> \<Union>S1} * N \<le> card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) + (card {B. preposthuman B \<and> B \<in> C} * N)" using indhyp by linarith
  from Suc.prems have "C \<in> S1 \<longrightarrow> card  ({B. preposthuman B} \<inter> (\<Union>{S. (RUNS C S)})) \<ge> N * card {B. B\<in>C \<and> preposthuman B}" by blast
  hence sf3: "card ({B. preposthuman B} \<inter> (\<Union>{S. (RUNS C S)})) \<ge> N * card {B. B\<in>C \<and> preposthuman B}" using obtC by blast
  have "{B. B\<in>C \<and> preposthuman B} = {B. preposthuman B \<and> B \<in> C}" by fast
  hence "card {B. B\<in>C \<and> preposthuman B} = card {B. preposthuman B \<and> B \<in> C}" by simp
  hence sf4: "card ({B. preposthuman B} \<inter> (\<Union>{S. (RUNS C S)})) \<ge> N * card {B. preposthuman B \<and> B \<in> C}" using sf3 by argo
  have "N * card {B. preposthuman B \<and> B \<in> C} = card {B. preposthuman B \<and> B \<in> C} * N" by algebra
  hence "card ({B. preposthuman B} \<inter> (\<Union>{S. (RUNS C S)})) \<ge> card {B. preposthuman B \<and> B \<in> C} * N" using sf4 by argo
  hence sf5: "card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) + (card {B. preposthuman B \<and> B \<in> C} * N) \<le> card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) + card  ({B. preposthuman B} \<inter> (\<Union>{S. (RUNS C S)}))" by linarith   
  hence sfineq: "card {B. preposthuman B \<and> B \<in> \<Union>S1} * N \<le>  card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) + card  ({B. preposthuman B} \<inter> (\<Union>{S. (RUNS C S)}))" using Suc.prems(4) Suc.prems(5) obtC using le_trans sf2 by blast 
  have "card (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}})))\<ge> card (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) + card ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S})" using Suc.prems(10) Suc.prems(3) obtC 
  proof -
    have a: "(({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<supseteq> ((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<union> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S}))" using Suc.prems(10) Suc.prems(3) obtC by blast
    have ff: "finite (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}})))" using finiteuniverse prepostisbeing
    proof -
      have subs: "(({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<subseteq> {B. being B}" using prepostisbeing by fast
      {assume red: "infinite (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}})))"
        from infinite_super have "\<And>S T. infinite S \<Longrightarrow> S \<subseteq> T \<Longrightarrow> infinite T" by force
        hence  "\<And>T. infinite (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<Longrightarrow> (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<subseteq> T  \<Longrightarrow> infinite T" by blast (*horribly slow*)
        hence "infinite (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<Longrightarrow> (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<subseteq> {B. being B} \<Longrightarrow> infinite {B. being B}" by blast
        hence "infinite {B. being B}" using subs red by blast
        hence False using finiteuniverse by simp}
      thus ?thesis by blast qed
   from card_mono have "\<And>S T. finite S \<Longrightarrow> S \<supseteq> T \<Longrightarrow> card S \<ge> card T" by auto
   hence "\<And>T. finite  (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<Longrightarrow>  (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<supseteq> T \<Longrightarrow> card  (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<ge> card T" by blast
   hence "finite  (({B. preposthuman B} \<inter> \<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<Longrightarrow>  (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<supseteq> (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<union> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S}) \<Longrightarrow> card  (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<ge> card ((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<union> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S}))" by presburger   
   hence  stupid1: "(({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<supseteq> (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<union> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S}) \<Longrightarrow> card  (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<ge> card ((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<union> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S}))" using ff by blast
   from a have "(({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<supseteq> (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<union> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S})" by blast   
   hence alm: "card  (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}))) \<ge> card ((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<union> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S}))" using stupid1 by blast   
   have "card ((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<union> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S})) \<ge>  card (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) + card ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S})" 
   proof -
     have aaa: "((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))) \<inter> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S})) = {}"
     proof - 
       {fix x
         assume "x \<in> (({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}})))"
         hence "x \<in>  \<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}})" by fast
         hence "\<exists>CC\<in>?othcivs. \<exists>SS. (RUNS CC SS) \<and> x \<in> SS" by blast
         then obtain CC SS where obtCCSS: "CC \<in> ?othcivs \<and> (RUNS CC SS) \<and> x \<in> SS" by auto  
         hence noteq: "CC \<noteq> C" using obtC by simp
         {assume "x \<in> \<Union>{S. RUNS C S}"
           hence "\<exists>SSS. (RUNS C SSS) \<and> x \<in> SSS" by blast
           then obtain SSS where obtSSS: "(RUNS C SSS) \<and> x \<in> SSS" by auto
           hence "SSS \<inter> SS = {}"
           proof -
             have aa: "SS \<in> \<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}" using obtCCSS by blast
             have bb: "SSS \<in> \<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}}" using obtSSS obtC by auto
             from noteq have "{S. RUNS C S} \<inter> {S. RUNS CC S} = {}" using obtCCSS Suc.prems(10) obtC by simp
             hence cc: "SS \<noteq> SSS" using obtSSS obtCCSS by blast
             thus ?thesis using aa bb Suc.prems by presburger (*slow*) qed    
           hence False using obtCCSS obtSSS by blast}
         hence "x \<notin> ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S})" by blast}
       thus ?thesis by blast (*horribly slow*) qed
     have bbb: "finite ((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))))"
     proof -
       have subss: "((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}})))) \<subseteq> {B. being B}" using prepostisbeing by force
       {assume "infinite ((({B. preposthuman B} \<inter>\<Union>(\<Union>{simset. \<exists>C\<in>?othcivs. simset = {S. (RUNS C S)}}))))"
         hence "infinite {B. being B}" using infinite_super subss by blast
        hence False using finiteuniverse by simp}
      thus ?thesis by blast qed
     have ccc: "finite ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S})"
     proof -
       have subss: "({B. preposthuman B} \<inter> \<Union>{S. RUNS C S}) \<subseteq> {B. being B}" using prepostisbeing by force
       {assume "infinite ({B. preposthuman B} \<inter> \<Union>{S. RUNS C S})"
         hence "infinite {B. being B}" using infinite_super subss by blast
        hence False using finiteuniverse by simp}
         thus ?thesis by blast qed 
       thus ?thesis using aaa bbb ccc card_Un_disjoint by fastforce qed
     thus ?thesis using alm by force qed
 hence "card {B. preposthuman B \<and> B\<in>(\<Union>S1)} * N \<le> card ( {B. preposthuman B} \<inter>(\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (RUNS C S)}})))" using sfineq by linarith 
  thus ?case  by blast
qed      



lemma simineqhelper4: "card {C. civilization C \<and> (C runs N sims)} = card {Sims. \<exists>C. C \<in>  {C. civilization C \<and> (C runs N sims)} \<and> Sims = {S. (C Runs S)}}"
proof -
  let ?S1 = "{C. civilization C \<and> C runs N sims}" 
  let ?S2 = "{Sims. (\<exists>C\<in>?S1. (Sims = {S. C Runs S}))}"
 have c: "card ?S1 = card ?S2"
  proof -
  have "inj_on (\<lambda>A. {C.  (A Runs  C)}) ?S1"
  proof- 
    {fix X Y
     {assume a1: "X \<in> ?S1 \<and> Y \<in> ?S1"
          and a: "(\<lambda>A. {C.  (A Runs  C)}) X = (\<lambda>A. {C.  (A Runs  C)}) Y"
       hence f1: "{C.  (X Runs  C)} = {C.  (Y Runs  C)}" by linarith 
       {assume red1: "X \<noteq> Y"
         hence empt: "{C.  (X Runs  C)} = {}" using f1 discrSim by auto         
         from a1 have "X runs N sims" by simp
         hence "card {S. X Runs S} > 0" using prettybig by auto
         hence "{S. X Runs S} \<noteq> {}" by force
         hence "\<exists>S. S \<in> {S. X Runs S}" by blast
         then obtain S where obtS: "S \<in> {S. X Runs S}" by auto
         hence "X Runs S" by blast
         hence False using empt by fast}
        hence "X = Y" by blast}}
     hence "(\<forall>x\<in> ?S1. \<forall>y\<in> ?S1. (\<lambda>A. {C.  (A Runs  C)}) x = (\<lambda>A. {C.  (A Runs  C)}) y \<longrightarrow> x = y)" by meson
     thus ?thesis using inj_on_def by fast qed  
   hence c1: "card ((\<lambda>A. {C. (A Runs C)}) ` ?S1) = card ?S1" by (rule card_image)
   have "((\<lambda>A. {C. (A Runs C)}) ` ?S1) = {Sims. \<exists>C. C \<in>  {C. civilization C \<and> (C runs N sims)} \<and> Sims = {S. (C Runs S)}}" by auto
   hence "card ((\<lambda>A. {C. (A Runs C)}) ` ?S1) = card ?S2" by auto
   thus ?thesis using c1 by presburger qed 
  thus ?thesis by meson 
qed

  
lemma simineqhelper26: "card ({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)}))* N \<le> card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>{C. civilization C \<and> (C runs N sims)}. simset = {S. (C Runs S)}})))"
proof -
  let ?S1 = "{C. civilization C \<and> (C runs N sims)}"
  have one: "finite ?S1" by (metis (no_types, lifting) card_infinite diffex eq_divide_eq of_nat_0)
  have two: "\<forall>C. finite {S. (C Runs S)}"
  proof - 
    {assume "\<exists>C. infinite {S. C Runs S}"
      then obtain C where obtC: "infinite {S. C Runs S}" by auto
      hence a:"infinite (\<Union>{S. C Runs S})" using finite_UnionD by blast
      have "\<And>x. x \<in> (\<Union>{S. C Runs S}) \<Longrightarrow> being x"  by (metis diffSimCiv onlyBeingsInCivs onlyBeingsInSims)
      hence "{B. being B} \<supseteq> (\<Union>{S. C Runs S})" by blast
      hence "infinite {B. being B}" using a using finite_subset by metis
      hence False using finiteuniverse by simp}
    thus ?thesis by auto qed     
  have three: "\<forall>C. C \<in> ?S1 \<longrightarrow> {S. C Runs S} \<noteq> {}"
  proof -
    {fix C
      assume "C\<in>?S1"
      hence "C runs N sims" by simp
      hence "card {S. C Runs S} > 0" using prettybig by linarith
      hence "{S. C Runs S} \<noteq> {}" by fastforce}
     thus ?thesis by blast qed 
    have four: "card ?S1 = s" by blast
    have five: "card {simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} = card ?S1" using  simineqhelper4 by simp
    have six: "\<forall>C. C \<in> ?S1 \<longrightarrow> card  ({B. preposthuman B} \<inter> (\<Union>{S. (C Runs S)})) \<ge> N * card {B. B\<in>C \<and> preposthuman B}" 
    proof -
      {fix D
        assume "D \<in> ?S1"
        hence "D runs N sims" by simp
        hence stupid1: "card {B. being B \<and> preposthuman B \<and> (\<exists>S. ( (D Runs S) \<and> B \<in> S))} \<ge> N *  card {B. being B \<and>  preposthuman B \<and> B \<in> D}" using simineqhelper2 by blast
        have  stupid2: "({B. preposthuman B} \<inter> (\<Union>{S. (D Runs S)})) \<supseteq>  {B. being B \<and> preposthuman B \<and> (\<exists>S. ( (D Runs S) \<and> B \<in> S))}" by auto
        have "{B. being B} \<supseteq> (\<Union>{S. (D Runs S)})" using RunsAnc ancsimIsSim onlyBeingsInSims by fastforce       
        hence "finite ( (\<Union>{S. (D Runs S)}))" using finiteuniverse by (metis infinite_super)
        hence "finite ({B. preposthuman B} \<inter> (\<Union>{S. (D Runs S)}))" by simp
        hence "card ({B. preposthuman B} \<inter> (\<Union>{S. (D Runs S)})) \<ge> card {B. being B \<and> preposthuman B \<and> (\<exists>S. ( (D Runs S) \<and> B \<in> S))}" using stupid2 card_mono by blast
        hence stupid3: "card  ({B. preposthuman B} \<inter> (\<Union>{S. (D Runs S)})) \<ge> N *card {B. being B \<and>  preposthuman B \<and> B \<in> D}" using stupid1 le_trans by blast
        have "{B. being B \<and>  preposthuman B \<and> B \<in> D} = {B. B\<in>D \<and> preposthuman B}"
        proof -
          have lr: "{B. being B \<and>  preposthuman B \<and> B \<in> D} \<subseteq> {B. B\<in>D \<and> preposthuman B}" by (simp add: Collect_mono_iff)
          have "{B. being B \<and>  preposthuman B \<and> B \<in> D} \<supseteq> {B. B\<in>D \<and> preposthuman B}"
          proof -
            {fix x 
              assume asm: "x \<in> {B. B\<in>D \<and> preposthuman B}"
             hence "being x" using diffSimCiv onlyBeingsInCivs onlyBeingsInSims by blast   
             hence "x \<in> {B. being B \<and>  preposthuman B \<and> B \<in> D}" using asm by simp}
           thus ?thesis by auto qed
         thus ?thesis using lr by simp qed
       hence "card {B. being B \<and>  preposthuman B \<and> B \<in> D} = card {B. B\<in>D \<and> preposthuman B}" by argo
       hence "N * card {B. being B \<and>  preposthuman B \<and> B \<in> D} = N * card {B. B\<in>D \<and> preposthuman B}" by argo
       hence  "card  ({B. preposthuman B} \<inter> (\<Union>{S. (D Runs S)})) \<ge> N * card {B. B\<in>D \<and> preposthuman B}" using stupid3 by argo}
     thus ?thesis by blast qed
   have seven: "\<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> ?S1 \<longrightarrow> D \<in> ?S1 \<longrightarrow> (C \<inter> D) = {})" using citizenship2 by blast
   have eight: "\<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> {simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} \<longrightarrow> D \<in> {simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} \<longrightarrow> (C \<inter> D) = {})"  by (smt Int_emptyI discrSim mem_Collect_eq) (*Warning: slow smt proof*) 
   have nine: "\<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> \<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} \<longrightarrow> D \<in> \<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} \<longrightarrow> (C \<inter> D) = {})"
   proof -
     {fix C D
       assume CnD: "C \<noteq> D"
       and Cin: "C \<in>  \<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}}"
       and Din: "D \<in> \<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}}"
       have SimC: "simulation C"
       proof -
         from Cin have "\<exists>Civ. C \<in> {S. Civ Runs S}" by fast
         then obtain Civ where obtCiv: "C \<in> {S. Civ Runs S}" by auto
         hence "Civ Runs C" by simp
         thus ?thesis using RunsAnc ancsimIsSim by simp qed   
       have SimD: "simulation D"
       proof -
         from Din have "\<exists>Civ. D \<in> {S. Civ Runs S}" by fast
         then obtain Civ where obtCiv: "D \<in> {S. Civ Runs S}" by auto
         hence "Civ Runs D" by simp
         thus ?thesis using RunsAnc ancsimIsSim by simp qed  
       from SimD SimC CnD have  "(C \<inter> D) = {}" by (metis disjoint_iff_not_equal everysiminasim onlyBeingsInSims)}
     thus ?thesis by blast qed
   have ten: "\<forall>C D. C \<noteq> D \<longrightarrow> C \<in> ?S1 \<longrightarrow> D \<in> ?S1 \<longrightarrow> {S. (C Runs S)} \<inter> {S. (D Runs S)} = {}" 
   proof -
     {fix C D
       assume noteq: "C \<noteq> D"
       and Cin: "C \<in> ?S1"
       and Din: "D \<in> ?S1"
       {assume "\<exists>S. S \<in> {S. (C Runs S)} \<and> S \<in> {S. (D Runs S)}"
         then obtain S where obtS: "S \<in> {S. (C Runs S)} \<and> S \<in> {S. (D Runs S)}" by auto
         hence "(C Runs S) \<and> (D Runs S)" by blast
         hence False using noteq discrSim by auto}
       hence " {S. (C Runs S)} \<inter> {S. (D Runs S)} = {}" by blast}
       thus ?thesis by blast qed
   have eleven: "\<forall>C\<in>?S1. finite C" using finiteuniverse by (metis (no_types, lifting) infinite_super mem_Collect_eq onlyBeingsInCivs subset_eq)      
from simineqhelper25 have "\<And>S1. finite S1 (*{C. RNS C}*)
\<Longrightarrow> \<forall>C. finite {S. (C Runs S)}
\<Longrightarrow> \<forall>C. C \<in> S1 \<longrightarrow> {S. C Runs S} \<noteq> {}
\<Longrightarrow> card S1 = (card ?S1)
\<Longrightarrow> card {simset. \<exists>C\<in>S1. simset = {S. (C Runs S)}} = card S1
\<Longrightarrow> \<forall>C. C \<in> S1 \<longrightarrow> card  ({B. preposthuman B} \<inter> (\<Union>{S. (C Runs S)})) \<ge> N * card {B. B\<in>C \<and> preposthuman B}
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> S1 \<longrightarrow> D \<in> S1 \<longrightarrow> (C \<inter> D) = {})
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> {simset. \<exists>C\<in>S1. simset = {S. (C Runs S)}} \<longrightarrow> D \<in> {simset. \<exists>C\<in>S1. simset = {S. (C Runs S)}} \<longrightarrow> (C \<inter> D) = {} )
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> \<Union>{simset. \<exists>C\<in>S1. simset = {S. (C Runs S)}} \<longrightarrow> D \<in> \<Union>{simset. \<exists>C\<in>S1. simset = {S. (C Runs S)}} \<longrightarrow> (C \<inter> D) = {})
\<Longrightarrow> \<forall>C D. C \<noteq> D \<longrightarrow> C \<in> S1 \<longrightarrow> D \<in> S1 \<longrightarrow> {S. (C Runs S)} \<inter> {S. (D Runs S)} = {}
\<Longrightarrow> \<forall>C\<in>S1. finite C
\<Longrightarrow> card {B. preposthuman B \<and> B\<in>(\<Union>S1)} * N \<le> card ( {B. preposthuman B} \<inter>(\<Union>(\<Union>{simset. \<exists>C\<in>S1. simset = {S. (C Runs S)}})))" by presburger 
hence "finite ?S1 (*{C. RNS C}*)
\<Longrightarrow> \<forall>C. finite {S. (C Runs S)}
\<Longrightarrow> \<forall>C. C \<in> ?S1 \<longrightarrow> {S. C Runs S} \<noteq> {}
\<Longrightarrow> card ?S1 = (card ?S1)
\<Longrightarrow> card {simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} = card ?S1
\<Longrightarrow> \<forall>C. C \<in> ?S1 \<longrightarrow> card  ({B. preposthuman B} \<inter> (\<Union>{S. (C Runs S)})) \<ge> N * card {B. B\<in>C \<and> preposthuman B}
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> ?S1 \<longrightarrow> D \<in> ?S1 \<longrightarrow> (C \<inter> D) = {})
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> {simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} \<longrightarrow> D \<in> {simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} \<longrightarrow> (C \<inter> D) = {} )
\<Longrightarrow> \<forall>C D. (C \<noteq> D \<longrightarrow> C \<in> \<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} \<longrightarrow> D \<in> \<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}} \<longrightarrow> (C \<inter> D) = {})
\<Longrightarrow> \<forall>C D. C \<noteq> D \<longrightarrow> C \<in> ?S1 \<longrightarrow> D \<in> ?S1 \<longrightarrow> {S. (C Runs S)} \<inter> {S. (D Runs S)} = {}
\<Longrightarrow> \<forall>C\<in>?S1. finite C
\<Longrightarrow> card {B. preposthuman B \<and> B\<in>(\<Union>?S1)} * N \<le> card ( {B. preposthuman B} \<inter>(\<Union>(\<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}})))" by presburger
  hence bl0: "card {B. preposthuman B \<and> B\<in>(\<Union>?S1)} * N \<le> card ( {B. preposthuman B} \<inter>(\<Union>(\<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}})))" using one two three four five six seven eight nine ten eleven by blast
have " {B. preposthuman B \<and> B\<in>(\<Union>?S1)} = ({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)}))" by blast
hence "card {B. preposthuman B \<and> B\<in>(\<Union>?S1)} * N = card ({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) * N" by argo
hence bl1: "card ({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) * N \<le> card ( {B. preposthuman B} \<inter>(\<Union>(\<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}})))" using bl0 by argo
have "( {B. preposthuman B} \<inter>(\<Union>(\<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}}))) =  ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>{C. civilization C \<and> (C runs N sims)}. simset = {S. (C Runs S)}})))" by blast
hence "card ( {B. preposthuman B} \<inter>(\<Union>(\<Union>{simset. \<exists>C\<in>?S1. simset = {S. (C Runs S)}}))) =  card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>{C. civilization C \<and> (C runs N sims)}. simset = {S. (C Runs S)}})))" by blast
thus ?thesis using bl1 by argo
qed      

lemma simineq: "card {B. being B \<and> simulated B \<and> preposthuman B} \<ge> N * s * H\<^sub>s"(*added an extra preposthuman here; Bostroms original "lemma" follows trivially*)
proof -                       
  have "({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) =  (( {B. being B \<and>  preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}))" 
  proof -
    have rl: "({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) \<supseteq>  (( {B. being B \<and>  preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}))" by blast
    have lr: "({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) \<subseteq>  (( {B. being B \<and>  preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}))" using prepostisbeing by auto
    thus ?thesis using rl by blast qed
  hence  "N * card ({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) = N * card (( {B. being B \<and>  preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}))" by argo
  hence "N * (card ({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) / s) * s = N * (card (( {B. being B \<and>  preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}))/ s) * s" using diffex by fastforce
  hence "N * (card ({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) / s) * s = N * H\<^sub>s * s" by blast
  hence  "card ({B. preposthuman B} \<inter> (\<Union>{C. civilization C \<and> (C runs N sims)})) * N =  H\<^sub>s * s * N" using diffex by simp
  hence a: "H\<^sub>s * s * N \<le> card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>{C. civilization C \<and> (C runs N sims)}. simset = {S. (C Runs S)}})))" using simineqhelper26 by linarith
  have b: "({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>{C. civilization C \<and> (C runs N sims)}. simset = {S. (C Runs S)}}))) \<subseteq>  {B. being B \<and> simulated B \<and> preposthuman B}"
    proof -
      {fix x
        assume asm: "x \<in>({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>{C. civilization C \<and> (C runs N sims)}. simset = {S. (C Runs S)}})))"
        hence aa: "preposthuman x" by blast
        hence bb: "being x" using prepostisbeing by simp
        from asm have "\<exists>C S. (C Runs S) \<and> x \<in> S" by blast
        then obtain C S where "(C Runs S) \<and> x \<in> S" by auto
        hence "simulation S \<and> x \<in> S" using ancsimIsSim RunsAnc by auto
        hence "simulated x" by blast
        hence "x \<in> {B. being B \<and> simulated B \<and> preposthuman B}" using aa bb by simp}
      thus ?thesis by blast qed
    have "finite {B. being B \<and> simulated B \<and> preposthuman B}" using finiteuniverse by simp
    hence "card ({B. preposthuman B} \<inter> (\<Union>(\<Union>{simset. \<exists>C\<in>{C. civilization C \<and> (C runs N sims)}. simset = {S. (C Runs S)}}))) \<le>  card {B. being B \<and> simulated B \<and> preposthuman B}" using b infinite_super by (simp add: card_mono)
    hence "H\<^sub>s * s * N \<le>  card {B. being B \<and> simulated B \<and> preposthuman B}" using a by force (*slow*)
    hence bl: "card {B. being B \<and> simulated B \<and> preposthuman B} \<ge> H\<^sub>s * s * N " by blast
    have "H\<^sub>s * s * N = N * s * H\<^sub>s" by fastforce
    thus ?thesis using bl by presburger
qed        

section "The math parts"    
text "First, a couple of lemmas that make life easier later on"

lemma leql1: "m > 0 \<Longrightarrow> (a::real) \<le> b \<Longrightarrow> m *a \<le> m * b" by simp 
lemma ll1: "m > 0 \<Longrightarrow> (a::real) < b \<Longrightarrow> m *a < m * b" by simp 
lemma leql2: "m > 0 \<Longrightarrow> a \<le> (b:: real) \<Longrightarrow> m * a \<le> m * b" by auto
lemma ll2: "m > 0 \<Longrightarrow> a < (b:: real) \<Longrightarrow> m * a < m * b" by auto
lemma ll3: "a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> (c::real) > 0 \<Longrightarrow> d > 0 \<Longrightarrow> ((a/ c) > (b/ d) \<Longrightarrow> (c /a < (d / b)))"
proof -
{assume a: " a > 0"
and b: "b > 0"
and c: "c > 0"
and d: "d > 0"
{assume leq: "(a/ c) > (b/ d)"
from a have a2: "(1/a) > 0" by simp
hence "(1/ a) * (a/ c) > (1/a) * (b/ d)" using leq ll2 by blast
hence "(1/ c) >  (b/ (a * d))" using a2 by force
hence "d * (1/ c) >  d * (b/ (a * d))" using d ll1 by meson
hence  "d / c  > b / a" using d by simp
hence "c * (d/ c) > c * (b/a)" using c ll1 by blast
hence ine1: "d > (c * b) / a" using c by fastforce      
from b have "1/ b > 0 " by fastforce
hence "(1/ b) * d > (1/b) * ((c * b) / a)" using ll1 ine1 by meson  
hence "d / b > c / a" using b by simp}
hence "(a/ c) > (b/ d) \<Longrightarrow> (c / a) < (d / b)" by simp}
  thus "a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> (c::real) > 0 \<Longrightarrow> d > 0 \<Longrightarrow> ((a/ c) > (b/ d) \<Longrightarrow> (c /a < (d / b)))" by blast
qed           
lemma leql3: "a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> (c::real) > 0 \<Longrightarrow> d > 0 \<Longrightarrow> ((a/ c) \<ge> (b/ d) \<Longrightarrow> (c /a \<le> (d / b)))" using ll3 by fastforce (*slow*)
lemma leql4: "a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> (c::real) > 0 \<Longrightarrow> d > 0 \<Longrightarrow> ((a/ c) \<ge> (b/ d) \<longleftrightarrow> (c /a \<le> (d / b)))" using leql3 by metis
lemma ll4: "a > 0 \<Longrightarrow> b > 0 \<Longrightarrow> (c::real) > 0 \<Longrightarrow> d > 0 \<Longrightarrow> ((a/ c) > (b/ d) \<longleftrightarrow> (c /a < (d / b)))" using ll3 by metis
lemma leql5: "(a::real) > 0 \<Longrightarrow> b > 0 \<Longrightarrow>(a \<ge> b \<longleftrightarrow> 1 /a \<le> (1 / b))" using leql4 by (smt frac_less2) (*Warning: Uses SMT*)
lemma ll5: "(a::real) > 0 \<Longrightarrow> b > 0 \<Longrightarrow>(a > b \<longleftrightarrow> 1 /a < (1 / b))" using ll4 by (smt frac_less2) (*Warning: Uses SMT*)
  

text "We will introduce the fraction of simulated beings vs. real beings" (*only use preposthumans here; contrary to Bostrom*)
abbreviation fsim:: real
  where "fsim \<equiv> card {B. being B \<and> simulated B \<and> preposthuman B} / card {B. being B \<and>  preposthuman B}"
    
lemma fsimmi: "fsim \<ge> (N * s * H\<^sub>s) / (N*s*H\<^sub>s + n * H\<^sub>n + s * H\<^sub>s)"
proof -  
  let ?sim = "card {B. being B \<and> simulated B \<and> preposthuman B }"
 from allbeings have denom: "card {B. being B \<and> real B \<and> preposthuman B } =  n * H\<^sub>n + s * H\<^sub>s" by algebra
  have  "card {B. being B \<and>  preposthuman B} = card {B. being B \<and> simulated B \<and> preposthuman B} + card {B. being B \<and> real B \<and> preposthuman B}"
  proof -
    have interb: "{B. being B \<and> simulated B \<and> preposthuman B} \<inter> {B. being B \<and>  preposthuman B \<and> real B} = {}" using diffSimCiv by auto
    have unionb: "{B. being B \<and> simulated B \<and> preposthuman B} \<union> {B. being B \<and> real B \<and> preposthuman B} = {B. being B \<and>  preposthuman B}" using diffSimCiv by fastforce     
    have finb: "finite {B. being B \<and> simulated B \<and> preposthuman B}" using finiteuniverse by simp
    have finb2: "finite {B. being B \<and> real B \<and> preposthuman B}" using finiteuniverse by simp
    from card_Un_disjoint have  "finite {B. being B \<and> simulated B \<and> preposthuman B} \<Longrightarrow> finite {B. being B \<and> real B \<and> preposthuman B} \<Longrightarrow> {B. being B \<and> simulated B \<and> preposthuman B} \<inter> {B. being B \<and>  preposthuman B \<and> real B} = {}
      \<Longrightarrow> card ({B. being B \<and> simulated B \<and> preposthuman B} \<union> {B. being B \<and>  real B \<and> preposthuman B}) =  card {B. being B \<and> simulated B \<and> preposthuman B} + card {B. being B \<and> real B \<and> preposthuman B }" by fast
      hence " card ({B. being B \<and> simulated B \<and> preposthuman B} \<union> {B. being B \<and>  real B \<and> preposthuman B}) =  card {B. being B \<and> simulated B \<and> preposthuman B} + card {B. being B \<and>  real B \<and> preposthuman B}" using interb finb finb2 by blast 
      thus ?thesis using unionb by argo qed   
  hence  "card {B. being B \<and> preposthuman B} = ?sim +  n * H\<^sub>n + s * H\<^sub>s" using denom by linarith
  hence eq1: "?sim /card {B. being B \<and> preposthuman B}  = ?sim / (?sim +  n * H\<^sub>n + s * H\<^sub>s)" by presburger
  from relbig have "\<And>y yy. y \<ge> 0 \<Longrightarrow> (n * H\<^sub>n + s * H\<^sub>s) \<ge> 0 \<Longrightarrow> (yy::real) \<ge> y \<Longrightarrow> yy / (yy + (n * H\<^sub>n + s * H\<^sub>s)) \<ge> y /(y + (n * H\<^sub>n + s * H\<^sub>s))" by blast 
  hence "\<And>yy.  N * s * H\<^sub>s \<ge> 0 \<Longrightarrow> (n * H\<^sub>n + s * H\<^sub>s) \<ge> 0 \<Longrightarrow> (yy::real) \<ge>  N * s * H\<^sub>s \<Longrightarrow> yy / (yy + (n * H\<^sub>n + s * H\<^sub>s)) \<ge>  N * s * H\<^sub>s /( N * s * H\<^sub>s + (n * H\<^sub>n + s * H\<^sub>s))" by blast 
  hence relbiginst: "N * s * H\<^sub>s \<ge> 0 \<Longrightarrow> (n * H\<^sub>n + s * H\<^sub>s) \<ge> 0 \<Longrightarrow> (?sim::real) \<ge> N * s * H\<^sub>s \<Longrightarrow> ?sim / (?sim + (n * H\<^sub>n + s * H\<^sub>s)) \<ge> N * s * H\<^sub>s /(N * s * H\<^sub>s + (n * H\<^sub>n + s * H\<^sub>s))" by blast
  have a: "n * H\<^sub>n + s * H\<^sub>s \<ge> 0" using diffex by force
  have b: "N * s * H\<^sub>s \<ge> 0" by force                                               
  hence inst2: "(?sim::real) \<ge> N * s * H\<^sub>s \<Longrightarrow> ?sim / (?sim + (n * H\<^sub>n + s * H\<^sub>s)) \<ge> N * s * H\<^sub>s /(N * s * H\<^sub>s + (n * H\<^sub>n + s * H\<^sub>s))" using relbiginst a by blast   
  from simineq have "(?sim::real) \<ge> N * s * H\<^sub>s" by blast
  hence "?sim / (?sim + (n * H\<^sub>n + s * H\<^sub>s)) \<ge> N * s * H\<^sub>s /(N * s * H\<^sub>s + (n * H\<^sub>n + s * H\<^sub>s))" using inst2 by blast  
  thus ?thesis using eq1 by argo
qed      
    
    
text "Now the (problematic!) assumptions for the math parts are introduced"

axiomatization where Hsnot0: "H\<^sub>s  > 0"
lemma Hnnotneg: "H\<^sub>n \<ge> 0" by simp 
axiomatization where snot0: "s > 0"
axiomatization where nnot0: "n > 0" (*Can be derived given that we know there exists something that is either a civilization 
or simulation (our world) and a few other assumptions.*)
    
lemma forg0:  "(1 + (1/N) * (1 + (n / s) * (N / 1000000))) > 0"
proof -
 from prettybig have N2: "1 / N  > 0" by simp   
 from prettybig have "(N / 1000000) > 0" by auto
 hence "(n / s) * (N / 1000000) > 0" using nnot0 snot0 by fastforce    
 hence "(1 + (n / s) * (N / 1000000)) > 0" by argo
 hence "(1/N) * (1 + (n / s) * (N / 1000000)) > 0" using N2 by fastforce    
  thus ?thesis by simp
qed      
    
lemma fsimineq: "fsim \<ge> 1 / (1 + (1/N) * (1 + (n / s) * (N / 1000000)))"  
proof -
have eq1: "(N * s * H\<^sub>s) / (N*s*H\<^sub>s + n * H\<^sub>n + s * H\<^sub>s) = 1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s))))" 
proof - 
  have "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) = 1 / (1 +   ((1/ N) * 1 + (1/ N) * ((n *H\<^sub>n) / (s * H\<^sub>s))))" by argo
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) =  1 / (1 +   ((1/ N) + (1/ N) * ((n *H\<^sub>n) / (s * H\<^sub>s))))" by argo
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) =  1 / (1 +   ((1/ N) +  ((1 * n *H\<^sub>n) / (N * s * H\<^sub>s))))" by simp
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) =  1 / (1 +   ((1/ N) +  (( n *H\<^sub>n) / (N * s * H\<^sub>s))))" by auto  
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) = ((N * s * H\<^sub>s) / (N * s * H\<^sub>s)) * (1 / (1 +   ((1/ N) +  (( n *H\<^sub>n) / (N * s * H\<^sub>s)))))" using prettybig snot0 Hsnot0 by force
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) = ((N * s * H\<^sub>s) * 1 / ((N * s * H\<^sub>s) * (1 +   ((1/ N) +  (( n *H\<^sub>n) / (N * s * H\<^sub>s))))))" by fastforce
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) = ((N * s * H\<^sub>s) / (((N * s * H\<^sub>s)  +   (N * s * H\<^sub>s) * ((1/ N) +  (( n *H\<^sub>n) / (N * s * H\<^sub>s))))))" by argo
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) = ((N * s * H\<^sub>s) / (((N * s * H\<^sub>s)  +    ((N * s * H\<^sub>s) * (1/ N) +  (N * s * H\<^sub>s)* (( n *H\<^sub>n) / (N * s * H\<^sub>s))))))" by argo    
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) = ((N * s * H\<^sub>s) / (((N * s * H\<^sub>s)  +    (((N * s * H\<^sub>s)/ N) +  (N * s * H\<^sub>s)* (( n *H\<^sub>n) / (N * s * H\<^sub>s))))))" by force   
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) = ((N * s * H\<^sub>s) / (((N * s * H\<^sub>s)  +    (((N * s * H\<^sub>s)/ N) +  (( (N * s * H\<^sub>s) *  n *H\<^sub>n) / (N * s * H\<^sub>s))))))" by force   
  hence "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) = ((N * s * H\<^sub>s) / (((N * s * H\<^sub>s)  +    ((( s * H\<^sub>s)) +  ((n *H\<^sub>n))))))" by force   
  thus ?thesis by simp qed    
  have ineq1: "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) \<ge> 1 / (1 + (1/N) * (1 + (n / s) * (N / 1000000)))"
  proof -
    have "(n / s) > 0" using nnot0 snot0 by simp   
    hence "(n / s) *  (H\<^sub>n / H\<^sub>s) \<le> ((n / s) *   (N / 1000000))" using quot leql1 by presburger
    hence "1 + ((n / s) *  (H\<^sub>n / H\<^sub>s)) \<le> (1 + ((n / s) *   (N / 1000000)))" by force
    hence a1:"1 + ((n * H\<^sub>n) /  (s * H\<^sub>s)) \<le> (1 + ((n / s) *   (N / 1000000)))" by auto
    from prettybig have N2: "1 / N  > 0" by simp   
    hence " (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s))) \<le> ( (1/N) * (1 + (n / s) * (N / 1000000)))" using leql2 a1 by meson  
    hence a2: "(1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) \<le>  (1 + (1/N) * (1 + (n / s) * (N / 1000000)))" by simp
    have a3: "(1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) > 0"
    proof - 
      from snot0 Hsnot0 have "s * H\<^sub>s > 0" using mult_pos_pos of_nat_0_less_iff by blast
      hence "(n *H\<^sub>n) / (s * H\<^sub>s) \<ge> 0" using nnot0 Hnnotneg by fastforce
      hence "( (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) > 0" by argo
      hence "( (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) > 0" using N2 by simp
      thus ?thesis by argo qed
    have "(1 + (1/N) * (1 + (n / s) * (N / 1000000))) > 0" using forg0 by simp      
    then show "1 / (1 + (1/ N) * (1 + ((n *H\<^sub>n) / (s * H\<^sub>s)))) \<ge> 1 / (1 + (1/N) * (1 + (n / s) * (N / 1000000)))" using a2 a3 leql5 by blast qed 
thus ?thesis using eq1 fsimmi by argo (*slow*)    
qed    


(*fsim \<ge> 99% \<Longrightarrow> one of the claims of the argument is true*)  

lemma fsimsmall:
assumes flow: "fsim < (99/100)"  
and Nhuge: "N > 9900"
shows "10000 * s < n"
proof -
from flow fsimineq have a1: "1 / (1 + (1/N) * (1 + (n / s) * (N / 1000000))) < (99/100)" by argo
  have a2: "((99::real)/ 100) > 0" by simp
  have a3: "(1 + (1/N) * (1 + (n / s) * (N / 1000000))) > 0" using forg0 by simp
  from ll4 have  "(1 + (1/N) * (1 + (n / s) * (N / 1000000))) > 0  \<Longrightarrow> (100::real) > 0 \<Longrightarrow> (1::real) > 0 \<Longrightarrow> (99::real) > 0 \<Longrightarrow> (((1 + (1/N) * (1 + (n / s) * (N / 1000000)))/ 1) > (100/ 99) \<longleftrightarrow> (1 /(1 + (1/N) * (1 + (n / s) * (N / 1000000))) < ((99::real) / 100)))" by blast
  hence "(((1 + (1/N) * (1 + (n / s) * (N / 1000000)))/ 1) > (100/ 99) \<longleftrightarrow> (1 /(1 + (1/N) * (1 + (n / s) * (N / 1000000))) < ((99::real) / 100)))" using a2 a3 by linarith    
  hence "(100/ 99) < (1 + (1/N) * (1 + (n / s) * (N / 1000000)))" using a1 by argo 
  hence "1 / 99 < (1/N) * (1 + (n / s) * (N / 1000000))" by simp
  hence "1 / 99 <  ((1/N) + (1/N) * (n / s) * (N / 1000000))" by argo
  hence "1 / 99 - 1/ N <  ((1/N) * (n / s) * (N / 1000000))" by linarith   
  hence "1 / 99 - 1/ N <  ( (n / s) * (1/N) *(N / 1000000))" by simp
  hence "1 / 99 - 1/ N <  ( (n / s) * (1 / 1000000))" using prettybig by simp
  hence a4: "1 / 99 - 1/ N <  n / (s * 1000000)"  by fastforce 
  (*Try0 says: Trying "simp", "auto", "blast", "metis", "argo", "linarith", "presburger", "algebra", "fast", "fastforce", "force", "meson", and "satx"... 
Assumptions:
1 / 99 - 1 / real N < real n / real s * (1 / 1000000)
  [1 / 99 - 1 / real N < real n / real s * (1 / 1000000)]
\<not> 1 / 99 - 1 / real N < real n / real (s * 1000000)
  [\<not> 1 / 99 - 1 / real N < real n / real (s * 1000000)]

Proved:
99 * real n / real s < 99000000 * real n / real s / 1000000
  [\<not> 1 / 99 - 1 / real N < real n / real (s * 1000000),
    1 / 99 - 1 / real N < real n / real s * (1 / 1000000)]
 
Linear arithmetic should have refuted the assumptions.
Please inform Tobias Nipkow. 
Assumptions:
1 / 99 - 1 / real N < real n / real s * (1 / 1000000)
  [1 / 99 - 1 / real N < real n / real s * (1 / 1000000)]
\<not> 1 / 99 - 1 / real N < real n / real (s * 1000000)
  [\<not> 1 / 99 - 1 / real N < real n / real (s * 1000000)]

Proved:
99 * real n / real s < 99000000 * real n / real s / 1000000
  [\<not> 1 / 99 - 1 / real N < real n / real (s * 1000000),
    1 / 99 - 1 / real N < real n / real s * (1 / 1000000)]
 
Linear arithmetic should have refuted the assumptions.
Please inform Tobias Nipkow. 
Try this: by fastforce
(fastforce: 0 ms; simp, auto, force: 15 ms)*)    
  from Nhuge have "1 / N < (1 / 9900)" by fastforce
  hence "\<And>m. m - (1 / N) > m - (1 / 9900)" by auto     
  hence a5: "(1/ 99::real) - (1 / N) > (1/99) - (1 / 9900)" by presburger
  have "(1/ 99::real) - (1 / 9900) = (1 / 100)" by fastforce    
  hence "(1/ 99::real) - (1 / N) > 1 / 100" using a5 by presburger
  hence "1 / 100 < n / (s * 1000000)" using a4 by argo (*slow*)
  thus "10000 * s < n" using snot0 by auto
qed
  
text "For the next steps we split n into the number of civilizations that reached a posthuman phase
but run less than N simulations and those that didn\<acute>t."
abbreviation a::nat 
where "a \<equiv> card {C. civilization C \<and> \<not> posthumansoc C}"
abbreviation b::nat 
where "b\<equiv> card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)}"

  
text "We need the following lemma for two different proofs"  
lemma finitecivs:  "finite {C. civilization C}"
  proof -
  {assume "infinite {C. civilization C}"
  hence nonfin: "infinite (\<Union> {C. civilization C})" by (meson finite_UnionD)
  have "\<And>B. B \<in> (\<Union> {C. civilization C}) \<Longrightarrow> being B " using onlyBeingsInCivs by auto
  hence "{B. being B} \<supseteq> (\<Union> {C. civilization C})" by blast
  hence "infinite {B. being B}" using nonfin infinite_super by auto     
  hence False using finiteuniverse by simp}
thus "finite {C. civilization C}" by auto
qed
  
lemma nab: "n = a + b" 
proof - 
    have on: "{C. civilization C \<and> \<not> posthumansoc C} \<inter> {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} = {}" by blast
    have "finite {C. civilization C}" using finitecivs by simp
  hence fin: "finite ({C. civilization C} - {C. C runs N sims})" by blast
  have "{C. civilization C \<and> \<not> posthumansoc C} = {C. civilization C \<and> \<not> posthumansoc C \<and> \<not>(C runs N sims)}" 
    by (metis (mono_tags, lifting) OnlyPostSim card_empty empty_Collect_eq leD prettybig)
  hence "{C. civilization C \<and> \<not> posthumansoc C} \<union>  {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} =  {C. civilization C \<and> \<not>(C runs N sims)}" by blast
  hence q: "{C. civilization C \<and> \<not> posthumansoc C} \<union>  {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} = {C. civilization C} - {C. C runs N sims}" by auto
  hence "finite ({C. civilization C \<and> \<not> posthumansoc C} \<union>  {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)})" using fin by presburger
  hence "card {C. civilization C \<and> \<not> posthumansoc C} + card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} = card ({C. civilization C \<and> \<not> posthumansoc C} \<union> {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)})"  using on card_Un_disjoint infinite_Un by fastforce
  hence "a + b = card ({C. civilization C \<and> \<not> posthumansoc C} \<union> {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)})" by blast
  hence "a + b = card ({C. civilization C} - {C. C runs N sims})" using q by auto     
  thus ?thesis by auto
qed      
  
(*b \<ge> 99 * s \<Longrightarrow> civs are unlikely to run anc sims*)  
 
lemma fsimb:
assumes flow: "fsim < (99/100)"  
and Nhuge: "N > 9900"
and blow: "b < 99 * s"
shows "9901 * s < a" 
proof -  
from fsimsmall have "10000 * s < n" using flow Nhuge by meson
hence "10000 * s < a + b" using nab by presburger
hence "10000 * s < a + (99 * s)" using blow by fastforce (*kind of slow*)       
thus ?thesis by auto
qed



      
lemma fsimfrac:
assumes flow: "fsim < (99/100)"  
and Nhuge: "N > 9900"
and blow: "b < 99 * s"
shows "card {C. civilization C \<and> \<not> posthumansoc C} / card {C. civilization C} \<ge> (99/100)" 
proof -  
  have "card {C. civilization C} = s + n"
  proof -
    have inter: "{C. civilization C \<and> (C runs N sims)} \<inter> ({C. civilization C} - {C. C runs N sims}) = {}" by blast
    have union: "{C. civilization C \<and> (C runs N sims)} \<union> ({C. civilization C} - {C. C runs N sims}) = {C. civilization C}" by auto
    thus ?thesis using inter finitecivs by (metis (no_types, lifting) card_Un_disjoint card_ge_0_finite finite_Diff snot0) qed     
  hence cardC: "card {C. civilization C} = s + a + b" using nab by algebra
  hence cc: "card {C. civilization C \<and> \<not> posthumansoc C} / card {C. civilization C} = a / (s + a + b)"  by presburger
  hence "a / card {C. civilization C} = a / (s + a + b)" using cardC by blast   
  hence cardfin: "card {C. civilization C \<and> \<not> posthumansoc C} / card {C. civilization C}= a / (s + a + b)" by blast
  have "s \<ge> 0" by auto
  hence on: "(s + a + b) < (s + a + 99 * s)" using blow by linarith    
  have tw: "a \<ge> 0" by simp
  hence "a / (s + a + b) \<ge> a / (s + a + 99 * s)" using on by (simp add: add_gr_0 frac_le)
  hence ine: "a / (s + a + b) \<ge> a / (100 * s + a)" by fastforce
  have three: "9901 * s \<le> a" using fsimb flow Nhuge blow by auto
  (*Try0 says: Trying "simp", "auto", "blast", "metis", "argo", "linarith", "presburger", "algebra", "fast", "fastforce", "force", "meson", and "satx"... 
Assumptions:
9900 < N
card {C. civilization C \<and> posthumansoc C \<and> \<not> N \<le> card {S. CRunsS}}
< 99 * card {C. civilization C \<and> N \<le> card {S. CRunsS}}
Real.real (card {B. simulated B}) / Real.real (card {B. preposthuman B}) < 99 / 100
9900 < N
card {C. civilization C \<and> posthumansoc C \<and> \<not> N \<le> card {S. CRunsS}}
< 99 * card {C. civilization C \<and> N \<le> card {S. CRunsS}}
\<not> Real.real (card {B. simulated B}) * 100 / Real.real (card {B. preposthuman B}) < 99
  [\<not> Real.real (card {B. simulated B}) * 100 / Real.real (card {B. preposthuman B})
      < 99]

Proved:
100 * Real.real (card {B. simulated B}) / Real.real (card {B. preposthuman B})
< Real.real (card {B. simulated B}) * 100 / Real.real (card {B. preposthuman B})
  [\<not> Real.real (card {B. simulated B}) * 100 / Real.real (card {B. preposthuman B})
      < 99]
 
Linear arithmetic should have refuted the assumptions.
Please inform Tobias Nipkow. 
Assumptions:
9900 < N
card {C. civilization C \<and> posthumansoc C \<and> \<not> N \<le> card {S. CRunsS}}
< 99 * card {C. civilization C \<and> N \<le> card {S. CRunsS}}
Real.real (card {B. simulated B}) / Real.real (card {B. preposthuman B}) < 99 / 100
9900 < N
card {C. civilization C \<and> posthumansoc C \<and> \<not> N \<le> card {S. CRunsS}}
< 99 * card {C. civilization C \<and> N \<le> card {S. CRunsS}}
\<not> Real.real (card {B. simulated B}) * 100 / Real.real (card {B. preposthuman B}) < 99
  [\<not> Real.real (card {B. simulated B}) * 100 / Real.real (card {B. preposthuman B})
      < 99]

Proved:
100 * Real.real (card {B. simulated B}) / Real.real (card {B. preposthuman B})
< Real.real (card {B. simulated B}) * 100 / Real.real (card {B. preposthuman B})
  [\<not> Real.real (card {B. simulated B}) * 100 / Real.real (card {B. preposthuman B})
      < 99]
 
Linear arithmetic should have refuted the assumptions.
Please inform Tobias Nipkow. *)
  have one: "a \<ge> 0" by force   
  have two: "(9901::real) * s \<ge> 0" by simp
  have four: "100 * s \<ge> 0" by blast
  let ?z = "100 * s"    
  from relsmall have "\<And>y z. 9901 * s \<ge> 0 \<Longrightarrow> z \<ge> 0 \<Longrightarrow> (9901::real) * s \<le> y \<Longrightarrow> (9901 * s) / ((9901 * s) + z) \<le> y /(y + z)" by force  
  hence "\<And>z. 9901 * s \<ge> 0 \<Longrightarrow> z \<ge> 0 \<Longrightarrow> (9901::real) * s \<le> a \<Longrightarrow> (9901 * s) / ((9901 * s) + z) \<le> a /(a + z)" by force      
  hence "9901 * s \<ge> 0 \<Longrightarrow> ?z \<ge> 0 \<Longrightarrow> (9901::real) * s \<le> a \<Longrightarrow> (9901 * s) / ((9901 * s) + ?z) \<le> a /(a + ?z)" by blast 
  hence ine2: "(9901 * s) / (((9901::real) * s) + 100 * s) \<le> a / (a + 100 * s )" using one two three by force  
  hence "(9901 * s) / ((10001::real) * s) \<le> a / (a + 100 * s )" by auto
  hence "9901 / (10001::real) \<le> a / (a + 100 * s )" using diffex by force
  hence "99 / 100 \<le>  a / (a + 100 * s )" by argo
  hence ff:"a / (a + 100 * s ) \<ge> 99 / 100" by blast
  from blow have one: "(a + 100 * s ) >  (s + a + b)" by presburger
  have "a \<ge> 0" by simp   
  hence "a / (a + 100 * s ) \<le>  a/ (s + a + b)" using one by (smt ine of_nat_add)
  hence "a/ (s + a + b) \<ge>  99 / 100" using ff by argo (*Again try0 gives a weird error(?) message*)
  thus ?thesis using cardfin by presburger
qed      

section "Additional (somewhat controversial) non-mathematical axioms"  
text "For the formalization of the argument we will introduce the predicates WeIn and  PIn. PIn X is to be interpreted
as \<acute>we are probably in (the set) X\<acute> and \<acute>WeIn X\<acute> means \<acute>we are in (set) X. This will approximate Bostroms credence operator Cr,
hopefully without replicating its problems. This can be read either doxastically (e.g.: we know we are in X/ We should consider ourselves
to be in X) or as set membership. Whether the argument is valid depends on whether there is a reading that
satisfies the axioms above."
  
  
consts weIn:: "'a set \<Rightarrow> bool"  
consts PIn:: "'a set \<Rightarrow> bool"  

text "It pays off to add the following two axioms."
axiomatization where PInSuper: "\<And>A B. PIn A \<Longrightarrow> A \<subseteq> B \<Longrightarrow> PIn B"  
  
text "Next we will introduce a predicate dunno. Dunno X is to be interpreted as `We have no
information as to whether we are a member of (set) X or not.`"  

consts dunno :: "'a set \<Rightarrow> bool"  

text "Again a useful axiom for working with membership uncertainty is needed."
axiomatization where dunnosub: "\<And>A B. dunno A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> dunno B"
  
text "Finally, we want to say that if we are a member of X then we are probably a member of X"
axiomatization where inPIn: "\<And>X. weIn X \<Longrightarrow> PIn X"  

text "And that if two sets make up another in which we are, we must be in one of the subsets."
axiomatization where inSubs: "\<And>A B. weIn (A \<union> B) \<Longrightarrow> (weIn A \<or> weIn B)"  
  
text "We can now formulate an axiom that is very close to Bostroms indifference principle.
It is not clear whether it is in fact correct, but it seems prima facie plausible."

axiomatization where INDP: "\<And> A B. weIn B \<Longrightarrow> B \<supseteq> A \<Longrightarrow> dunno A \<Longrightarrow> (card A) / (card B) \<ge> (99/100) \<Longrightarrow> PIn A"

text "For the proof to go through smoothly we will add a last unwieldy but ultimately unproblematic axiom."
axiomatization where inSimSoSim: "weIn {S. simulation S} \<Longrightarrow> weIn {B. being B \<and> simulated B}"  
  
text "Given the assumptions in Bostroms Appendix and a couple of \<acute>dunno statements\<acute>. we can now derive a conclusion similar to Bostrom\<acute>s."
  
section "The Argument"  
theorem SimulationArgumentFirstPatch:
assumes Nhuge: "N > 9900"
  
assumes wepre: "weIn  {B. being B \<and>  preposthuman B}"   
and dunnosim: "dunno {B. being B \<and> simulated B \<and> preposthuman B}"

assumes wesimorciv: "weIn {CS. civilization CS \<or> simulation CS}"
and dunnociv: "dunno {C. \<not> posthumansoc C}"

shows "(PIn {C. civilization C \<and> \<not> posthumansoc C}) \<or> PIn {B. being B \<and> simulated B} \<or> card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} \<ge> (99/100)"  
proof -
{assume fsimb99: "card {B. being B \<and> simulated B \<and> preposthuman B} / card {B. being B \<and>  preposthuman B} \<ge> (99/100)"
have "{B. being B \<and> simulated B \<and> preposthuman B} \<subseteq> {B. being B \<and>  preposthuman B}" by auto
hence prepsim: "PIn {B. being B \<and> simulated B \<and> preposthuman B}" using wepre dunnosim fsimb99 INDP by blast
from PInSuper have "PIn {B. being B \<and> simulated B \<and> preposthuman B} \<Longrightarrow> {B. being B \<and> simulated B \<and> preposthuman B} \<subseteq> {B. being B \<and> simulated B} \<Longrightarrow> PIn {B. being B \<and> simulated B}" by auto  
hence "PIn {B. being B \<and> simulated B}" using prepsim by auto
hence "(PIn {C. civilization C \<and> \<not> posthumansoc C}) \<or> PIn {B. being B \<and> simulated B} \<or> card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} \<ge> (99/100)" by blast}
  moreover
{assume fsims99: "card {B. being B \<and> simulated B \<and> preposthuman B} / card {B. being B \<and>  preposthuman B} < (99/100)"   
    {assume "card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} \<ge> (99/100)"
hence "(PIn {C. civilization C \<and> \<not> posthumansoc C}) \<or> PIn {B. being B \<and> simulated B} \<or> card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} \<ge> (99/100)" by blast}
    moreover
    {assume flikessim:"card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} < (99/100)"  
      have "card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} = b / (b + s)"
       proof - 
         have z: "card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} = b" by blast
         have "card {C. civilization C \<and> posthumansoc C} = card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} + card {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)}"
         proof -
           have "{C. civilization C \<and> posthumansoc C} = {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} \<union> {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)}" by blast
           hence cunion: "card {C. civilization C \<and> posthumansoc C} = card ({C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} \<union> {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)})" by argo
           have fina: "finite {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)}" using finitecivs by simp
           have finb: "finite {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)}" using finitecivs by simp
           have inter: "{C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} \<inter> {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)} = {}" by blast
           from fina finb inter have "card ({C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} \<union> {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)}) =  card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} + card {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)}"
               using card_Un_disjoint by fast
           thus ?thesis using cunion by argo qed 
         hence bplus: "card {C. civilization C \<and> posthumansoc C} = b + card {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)}" by blast
         have "{C. civilization C \<and> posthumansoc C \<and> (C runs N sims)} =  {C. civilization C \<and> (C runs N sims)}"
         proof -
           {fix x
             assume asm: "x \<in>{C. civilization C \<and> (C runs N sims)}"
             hence "card {S. x Runs S} > 0" using prettybig by fastforce
             hence "{S. x Runs S} \<noteq> {}" by fastforce
             hence "\<exists>S. x Runs S" by blast
             hence "posthumansoc x" using OnlyPostSim by auto
             hence "x \<in>{C. civilization C \<and> posthumansoc C \<and> (C runs N sims)}" using asm by simp}
           thus ?thesis by blast qed
         hence "card {C. civilization C \<and> posthumansoc C \<and> (C runs N sims)} = s" by argo
         hence "card {C. civilization C \<and> posthumansoc C} = b + s" using bplus by argo     
         thus ?thesis using z by presburger qed  
      hence ine1: "b / (b + s) < (99/100)" using flikessim by presburger
      hence blow: "b < 99 * s"
      proof -
        have sg0: "s \<ge> 0" by simp
        hence s99g0: "99 * s \<ge> 0" by simp    
        {assume "b \<ge> 99 * s"
          hence ine: "99 * s \<le> b" by blast
          from relsmall have "\<And>y z. (99 * s) \<ge> 0 \<Longrightarrow> z \<ge> 0 \<Longrightarrow> (99 * s) \<le> y \<Longrightarrow> (99 * s) / ((99 * s) + z) \<le> y /(y + z)" by simp
          hence "\<And>z. (99 * s) \<ge> 0 \<Longrightarrow> z \<ge> 0 \<Longrightarrow> (99 * s) \<le> b \<Longrightarrow> (99 * s) / ((99 * s) + z) \<le> b /(b + z)" by fastforce
          hence "(99 * s) \<ge> 0 \<Longrightarrow> s \<ge> 0 \<Longrightarrow> (99 * s) \<le> b \<Longrightarrow> (99 * s) / ((99 * s) + s) \<le> b /(b + s)" by blast
          hence "(99 * s) / ((99 * s) + s) \<le> b / (b + s)" using ine sg0 s99g0 by blast
          hence "99 / 100 \<le> b / (b + s)" using diffex by force
          hence False using ine1 by argo}  
         thus ?thesis by fastforce qed    
      hence fracdoom: "card {C. civilization C \<and> \<not> posthumansoc C} / card {C. civilization C} \<ge> (99/100)" using Nhuge fsims99 fsimfrac by blast      
      have "{CS. civilization CS \<or> simulation CS} = {C. civilization C} \<union> {S. simulation S}" by auto
      hence  "weIn ({C. civilization C} \<union> {S. simulation S})" using wesimorciv by metis
      hence disj: "weIn  {C. civilization C} \<or> weIn  {S. simulation S}" using inSubs by blast
      have "(PIn {C. civilization C \<and> \<not> posthumansoc C}) \<or> PIn {B. being B \<and> simulated B} \<or> card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} \<ge> (99/100)" 
       proof - 
       {assume red: "\<not> ((PIn {C. civilization C \<and> \<not> posthumansoc C}) \<or> PIn {B. being B \<and> simulated B} \<or> card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} \<ge> (99/100))"
        {assume  "weIn  {S. simulation S}"
        hence "weIn {B. being B \<and> simulated B}" using inSimSoSim by simp
        hence "PIn {B. being B \<and> simulated B}" using inPIn by auto
        hence False using red by blast}
       hence weciv: "weIn {C. civilization C}" using disj by auto 
       from dunnosub have "\<And>B. dunno {C. \<not> posthumansoc C} \<Longrightarrow> B \<subseteq> {C. \<not> posthumansoc C} \<Longrightarrow> dunno B" by auto
       hence "dunno {C. \<not> posthumansoc C} \<Longrightarrow> {C. civilization C \<and> \<not> posthumansoc C} \<subseteq> {C. \<not> posthumansoc C} \<Longrightarrow> dunno {C. civilization C \<and> \<not> posthumansoc C}" by auto 
       hence dunnopost: "dunno {C. civilization C \<and> \<not> posthumansoc C}" using dunnociv by fast
       from INDP have "\<And>B. weIn B \<Longrightarrow> B \<supseteq> {C. civilization C \<and> \<not> posthumansoc C} \<Longrightarrow> dunno {C. civilization C \<and> \<not> posthumansoc C} \<Longrightarrow> (card {C. civilization C \<and> \<not> posthumansoc C}) / (card B) \<ge> (99/100) \<Longrightarrow> PIn {C. civilization C \<and> \<not> posthumansoc C}" by blast
       hence "weIn {C. civilization C} \<Longrightarrow> {C. civilization C} \<supseteq> {C. civilization C \<and> \<not> posthumansoc C} \<Longrightarrow> dunno {C. civilization C \<and> \<not> posthumansoc C} \<Longrightarrow> (card {C. civilization C \<and> \<not> posthumansoc C}) / (card {C. civilization C}) \<ge> (99/100) \<Longrightarrow> PIn {C. civilization C \<and> \<not> posthumansoc C}" by blast
       hence "PIn {C. civilization C \<and> \<not> posthumansoc C}" using weciv fracdoom dunnopost by blast 
       hence False using red by argo}
      thus ?thesis by blast qed}
     ultimately have "(PIn {C. civilization C \<and> \<not> posthumansoc C}) \<or> PIn {B. being B \<and> simulated B} \<or> card {C. civilization C \<and> posthumansoc C \<and> \<not>(C runs N sims)} / card {C. civilization C \<and> posthumansoc C} \<ge> (99/100)" by argo}
ultimately show ?thesis  by argo
qed       
  
 end 