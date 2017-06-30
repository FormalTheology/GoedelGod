theory Appendix
  
  imports Complex_Main
    
begin
typedecl b (*Things in the world*)

section "Useful Lemmas for the upcoming proofs"  
  

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
  
lemma bigunionmult: "\<And>U. (card (U::'a set set) = p \<Longrightarrow>
  (\<And>S. S \<in> U \<Longrightarrow> (card S \<ge> q)) \<Longrightarrow> (\<And>S. S \<in> U \<Longrightarrow> (finite S)) \<Longrightarrow>
(\<And>S T. (S \<in> U \<Longrightarrow> T \<in> U \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {})) \<Longrightarrow> card (\<Union>U) \<ge> p * q)"
  proof (induct p)
    case 0
    then show ?case using card_eq_0_iff card_empty  finite_UnionD by linarith 
  next
    case (Suc p)
    from Suc.prems have cd: "card U = Suc p" by simp
    hence "U \<noteq> {}" by auto
    hence "\<exists>S. S  \<in> U" by auto
    then obtain S where obtS: "S \<in> U" by auto
    let ?nU = "U - {S}"
    from obtS cd have "card (?nU) = p" by (simp add: card_Diff_subset)
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

text "Conversely we need that a simulation contains only beings (see above)."  
axiomatization where onlyBeingsInSims: "(B \<in> S \<and> simulation S) \<longrightarrow> being B"  

text "The same goes for civilizations"
axiomatization where onlyBeingsInCivs: "(B \<in> C \<and> civilization C) \<longrightarrow> being B"  
  
text "Next we need to make sure that the number of simulated people in an ancestor simulation
is equal to the preposthuman population of the simulation." (*N.B.: It is not clear whether this is the correct approach.
Since not all simulations that are running have "gotten to the point" where really all beings
are already simulated*)  
axiomatization where sizeofsims: "(A Runs S) \<longrightarrow> (ancsimulation S \<and> card S = card {B. (being B) \<and> (B \<in> A) \<and> (preposthuman B)})"  

text "We also need to make sure that there are no beings that are neither real nor simulated."  
axiomatization where realorsim: "being (x) \<Longrightarrow> ((\<exists>C. (x \<in> C \<and> civilization C)) \<or> (\<exists>S. (simulation S \<and> x \<in> S)))"  
  
text "And we want that we only have a finite number of beings in our universe"  
axiomatization where finiteuniverse: "finite {B. being B}"  
  
  
  (* Ignore these for now.
axiomatization where civreal: "(\<forall>B. (\<exists> C. (B::b) \<in> C \<and> civilization C) \<longleftrightarrow> real B)"
axiomatization where civnotempt: "civilization S \<Longrightarrow> (\<exists>b. (being b \<and> b \<in> S))"  
*)
axiomatization where citizenship: "\<forall>B. (real B \<longrightarrow> (\<exists>C. (civilization C \<and> B \<in> C)) \<and> (\<forall>D. ((civilization D \<and> B \<in> D) \<longrightarrow> B = C)))"

  
text "Let N be a very large number such that there have been s civilizations 
that have run at least N ancestor simulations each"   
consts N::nat       
axiomatization where prettybig: "N > 0"  

text "We also need that two different societies cannot run the same simulation."
axiomatization where DiffVivDiffSim: "(A \<noteq> B) \<Longrightarrow> ((A Runs S) \<and> (B Runs T)) \<Longrightarrow> (S \<noteq> T)"

text "We will call a society posthuman iff there is a member in it that is posthuman."  
abbreviation posthumansoc:: "b set \<Rightarrow> bool"
  where "posthumansoc C \<equiv> \<exists>B\<in>C. (posthuman B)"
text "We then postulate that only posthuman societies can run (ancestor) simulations."
axiomatization where OnlyPostSim: "C Runs S \<Longrightarrow> posthumansoc C"  
  
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

  
lemma "{B. simulated B} \<supseteq> {B. ancsimulated B}" using ancsimIsSim by auto
lemma "{B. ancsimulated B} \<supseteq> {B. \<exists>S. B \<in> S \<and>  (\<exists>C. (C Runs S) \<and> (C runs N sims))}"  using sizeofsims by force 

lemma simsize2: "C Runs S \<Longrightarrow> card S = card {B. being B \<and>  preposthuman B \<and> B \<in> C}" 
proof -
  assume a1: "C Runs S"
  have "\<forall>p pa. (\<exists>b. (p (b::b) \<or> pa b) \<and> (\<not> p b \<or> \<not> pa b)) \<or> Collect p = Collect pa"
    by (metis Collect_cong) (* 0.0 ms *)
  then obtain bb :: "(b \<Rightarrow> bool) \<Rightarrow> (b \<Rightarrow> bool) \<Rightarrow> b" where
      f2: "\<forall>p pa. (p (bb p pa) \<or> pa (bb p pa)) \<and> (\<not> p (bb p pa) \<or> \<not> pa (bb p pa)) \<or> Collect p = Collect pa"
    by metis (* 31 ms *)
  have f3: "card S = card {b. being b \<and> b \<in> C \<and> preposthuman b}"
    using a1 sizeofsims by blast (* 0.0 ms *)
  then have "(being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<and> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<in> C \<and> preposthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))) \<and> card S = card {b. being b \<and> b \<in> C \<and> preposthuman b} \<and> preposthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<and> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> \<not> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C \<or> posthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))"
    by blast (* 0.0 ms *)
  moreover
  { assume "\<not> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C \<or> posthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))"
    then have "(\<not> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> posthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C) \<and> (\<not> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C \<or> posthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))) \<or> card S = card {b. being b \<and> preposthuman b \<and> b \<in> C}"
      by blast (* 0.0 ms *) }
  moreover
  { assume "(being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<and> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<in> C \<and> preposthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))) \<and> card S = card {b. being b \<and> b \<in> C \<and> preposthuman b} \<and> preposthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<and> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))"
    moreover
    { assume "\<exists>p. (being (bb p (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<and> preposthuman (bb p (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<and> bb p (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<in> C) \<and> card S = card (Collect p) \<and> p (bb p (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))"
      then have ?thesis
        using f2 by (metis (lifting)) (* 78 ms *) }
    ultimately have "(\<not> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> posthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C) \<and> (\<not> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C \<or> posthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))) \<or> card S = card {b. being b \<and> preposthuman b \<and> b \<in> C}"
      by (metis (lifting)) (* 46 ms *) }
  moreover
  { assume "(\<not> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> posthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C) \<and> (\<not> being (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C \<or> posthuman (bb (\<lambda>b. being b \<and> b \<in> C \<and> preposthuman b) (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)))"
    then have "\<exists>p. card S = card (Collect p) \<and> (\<not> being (bb p (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> posthuman (bb p (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C)) \<or> bb p (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C) \<notin> C) \<and> \<not> p (bb p (\<lambda>b. being b \<and> preposthuman b \<and> b \<in> C))"
      using f3 by blast (* 15 ms *)
    then have ?thesis
      using f2 by (metis (lifting)) (* 109 ms *) }
  ultimately show ?thesis
    by satx (* 46 ms *)
qed

    
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
   
lemma "card {B. being B \<and> simulated B} \<ge> N * s * H\<^sub>s" sorry(*Something went wrong; I will fix this ASAP*)
(*proof-
  let ?civs = "{C. civilization C \<and> C runs N sims}"
  have car1: "card ?civs = s" by simp
  have bigun: "{Sim. (\<exists>C. C \<in> ?civs \<and> (C Runs Sim))} = \<Union> {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})}" by auto 
  have "inj_on (\<lambda>A. {C.  (A Runs  C)}) ?civs"
    proof -
     {fix X Y
     {assume a1: "X \<in> ?civs \<and> Y \<in> ?civs"
          and a: "(\<lambda>A. {C.  (A Runs  C)}) X = (\<lambda>A. {C.  (A Runs  C)}) Y"
       hence f1: "{C.  (X Runs  C)} = {C.  (Y Runs  C)}" by linarith 
       {assume red1: "X \<noteq> Y"
         hence empt: "{C.  (X Runs  C)} = {}" using f1 DiffVivDiffSim by blast
         from a1 have "X runs N sims" by simp
         hence "card {S. X Runs S} > 0" using prettybig by auto
         hence "{S. X Runs S} \<noteq> {}" by force
         hence "\<exists>S. S \<in> {S. X Runs S}" by blast
         then obtain S where obtS: "S \<in> {S. X Runs S}" by auto
         hence "X Runs S" by blast
         hence False using empt by fast}
        hence "X = Y" by blast}}
     hence "(\<forall>x\<in> ?civs. \<forall>y\<in> ?civs. (\<lambda>A. {C.  (A Runs  C)}) x = (\<lambda>A. {C.  (A Runs  C)}) y \<longrightarrow> x = y)" by meson
     thus ?thesis using inj_on_def by fast qed  
   hence c1: "card ((\<lambda>A. {C. (A Runs C)}) ` ?civs) = card ?civs" by (rule card_image)
   have "{simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} = ((\<lambda>A. {C. (A Runs C)}) ` ?civs)" by blast
   hence "card {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} = card ?civs" using c1 by argo 
   hence a1: "card {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} = s" by blast
   have a2: "\<And>S. S \<in> {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} \<Longrightarrow> (card S \<ge> N)" by fast
   have a3: "(\<And>S. S \<in> {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} \<Longrightarrow> (finite S))"
   proof - 
     {fix S
     {assume asm: "S \<in> {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})}"
       hence "\<exists>C. S = {S. C Runs S}" by auto
       then obtain C where obtC: "S = {S. C Runs S}" by auto
       have "finite {S. C Runs S}" using finiteuniverse  asm linorder_not_le obtC prettybig by fastforce   
       hence "finite S" using obtC by simp}
       hence " S \<in> {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} \<Longrightarrow> (finite S)" by blast}
     then show "(\<And>S. S \<in> {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} \<Longrightarrow> (finite S))" by blast qed
  have a4: "\<And>S T. (S \<in> {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} \<Longrightarrow> T \<in> {simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})} \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {})"
  proof -
    fix S :: "b set set" and T :: "b set set"
    assume a1: "S \<noteq> T"
    assume a2: "S \<in> {simset. \<exists>C\<in>{C. civilization C \<and> N \<le> card {S. C Runs S}}. simset = {S. C Runs S}}"
    assume a3: "T \<in> {simset. \<exists>C\<in>{C. civilization C \<and> N \<le> card {S. C Runs S}}. simset = {S. C Runs S}}"
  have f4: "\<exists>B. B \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> S = Collect (CivRunsSim B)"
    using a2 by blast (* 0.0 ms *)
  obtain BB :: "b set set \<Rightarrow> b set" where
      f5: "\<forall>B. ((\<nexists>Ba. Ba \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> B = Collect (CivRunsSim Ba)) \<or> BB B \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> B = Collect (CivRunsSim (BB B))) \<and> ((\<exists>Ba. Ba \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> B = Collect (CivRunsSim Ba)) \<or> (\<forall>Ba. Ba \<notin> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<or> B \<noteq> Collect (CivRunsSim Ba)))"
    by moura (* 15 ms *)
  then have f6: "((\<nexists>B. B \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> S = Collect (CivRunsSim B)) \<or> BB S \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> S = Collect (CivRunsSim (BB S))) \<and> ((\<exists>B. B \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> S = Collect (CivRunsSim B)) \<or> (\<forall>B. B \<notin> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<or> S \<noteq> Collect (CivRunsSim B)))"
    by presburger (* 0.0 ms *)
  have f7: "\<forall>B Ba p pa. (\<not> B \<subseteq> Ba \<or> (\<exists>Ba. ((Ba::b set) \<in> B \<and> p Ba) \<and> \<not> pa Ba)) \<or> B \<inter> Collect p \<subseteq> Ba \<inter> Collect pa"
    by (meson Int_Collect_mono) (* 0.0 ms *)
  obtain BBa :: "(b set \<Rightarrow> bool) \<Rightarrow> (b set \<Rightarrow> bool) \<Rightarrow> b set set \<Rightarrow> b set" where
    "\<forall>x0 x1 x3. (\<exists>v4. (v4 \<in> x3 \<and> x1 v4) \<and> \<not> x0 v4) = ((BBa x0 x1 x3 \<in> x3 \<and> x1 (BBa x0 x1 x3)) \<and> \<not> x0 (BBa x0 x1 x3))"
    by moura (* 0.0 ms *)
  then have f8: "\<forall>B Ba p pa. (\<not> B \<subseteq> Ba \<or> (BBa pa p B \<in> B \<and> p (BBa pa p B)) \<and> \<not> pa (BBa pa p B)) \<or> B \<inter> Collect p \<subseteq> Ba \<inter> Collect pa"
    using f7 by presburger (* 31 ms *)
  have f9: "S \<subseteq> S"
    by (metis Int_lower1 inf.idem) (* 0.0 ms *)
  have "T \<in> {B. \<exists>Ba. Ba \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> B = Collect (CivRunsSim Ba)}"
    using a3 by meson (* 0.0 ms *)
  then have "\<exists>B. B \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> T = Collect (CivRunsSim B)"
    by blast (* 0.0 ms *)
  then have f10: "BB T \<in> {B. civilization B \<and> N \<le> card (Collect (CivRunsSim B))} \<and> T = Collect (CivRunsSim (BB T))"
    using f5 by blast (* 0.0 ms *)
  then have "BB S \<noteq> BB T"
    using f6 f4 a1 by (metis (no_types)) (* 15 ms *)
  moreover
  { assume "BB S \<noteq> BB T \<and> BB S Runs BBa (inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {})) (CivRunsSim (BB T)) S"
    then have "BBa (inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {})) (CivRunsSim (BB T)) S \<notin> S \<or> \<not> BB T Runs BBa (inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {})) (CivRunsSim (BB T)) S \<or> inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {}) (BBa (inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {})) (CivRunsSim (BB T)) S)"
      by (meson DiffVivDiffSim) (* 0.0 ms *) }
  ultimately have "BBa (inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {})) (CivRunsSim (BB T)) S \<notin> S \<or> \<not> BB T Runs BBa (inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {})) (CivRunsSim (BB T)) S \<or> inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {}) (BBa (inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {})) (CivRunsSim (BB T)) S)"
    using f6 f4 by blast (* 31 ms *)
  then have "S \<inter> Collect (CivRunsSim (BB T)) \<subseteq> S \<inter> Collect (inf (\<lambda>B. B \<in> S) (\<lambda>B. B \<in> {}))"
    using f9 f8 by meson (* 15 ms *)
  then show "S \<inter> T = {}"
    using f10 by blast (* 0.0 ms *)qed     
    let ?U = "{simset. (\<exists>C \<in> ?civs. simset = {S. (C Runs S)})}"
 have impl1: "\<And>U. (card U = s \<Longrightarrow>
  (\<And>S. S \<in> U \<Longrightarrow> (card S \<ge> N)) \<Longrightarrow> (\<And>S. S \<in> U \<Longrightarrow> (finite S)) \<Longrightarrow>
(\<And>S T. (S \<in> U \<Longrightarrow> T \<in> U \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {})) \<Longrightarrow> card (\<Union>U) \<ge> s * N)" by (simp add: bigunionmult)
 hence "card ?U = s \<Longrightarrow>
  (\<And>S. S \<in> ?U \<Longrightarrow> (card S \<ge> N)) \<Longrightarrow> (\<And>S. S \<in> ?U \<Longrightarrow> (finite S)) \<Longrightarrow>
(\<And>S T. (S \<in> ?U \<Longrightarrow> T \<in> ?U \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {})) \<Longrightarrow> card (\<Union>?U) \<ge> s * N" 
(*Not entirely sure what is happening here; Not even rule_tac with allE can prove this in one step.*)
 proof -
   {assume boo1: "card ?U = s"
    and boo2: "(\<And>S. S \<in> ?U \<Longrightarrow> (card S \<ge> N))"
    and boo3: "(\<And>S. S \<in> ?U \<Longrightarrow> (finite S))"
    and boo4: "(\<And>S T. (S \<in> ?U \<Longrightarrow> T \<in> ?U \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {}))"
    {assume red: "\<not>  card (\<Union>?U) \<ge> s * N"  
    hence False using boo1 boo2 boo3 boo4 impl1 by (metis (no_types, lifting))}
    hence "card (\<Union>?U) \<ge> s * N" by blast}  
    thus "card ?U = s \<Longrightarrow>
  (\<And>S. S \<in> ?U \<Longrightarrow> (card S \<ge> N)) \<Longrightarrow> (\<And>S. S \<in> ?U \<Longrightarrow> (finite S)) \<Longrightarrow>
(\<And>S T. (S \<in> ?U \<Longrightarrow> T \<in> ?U \<Longrightarrow> S \<noteq> T \<Longrightarrow> S \<inter> T = {})) \<Longrightarrow> card (\<Union>?U) \<ge> s * N" by blast qed 
hence cd3: "card (\<Union>?U) \<ge> s * N" using a1 a2 a3 a4 by blast     
let ?S = "\<Union>?U" (*Beings inside the simulation*)     
from bigun have "?S = {Sim. (\<exists>C. C \<in> ?civs \<and> (C Runs Sim))}" by blast  
hence "card \Unio?S = card "
  
  
  have "card ?S \<ge> card?U * H\<^sub>s"
  proof -
    {assume "infinite ?U"
      hence "card ?S \<ge> card?U * H\<^sub>s" by auto}
    moreover
      {assume as1: "finite ?U"
        have as2: "\<forall>S\<in>?U. finite S" using a3 by blast
        have as3: "\<forall>S T. (S \<noteq> T) \<longrightarrow> (S \<in> ?U) \<longrightarrow> (T \<in> ?U) \<longrightarrow>  (S \<inter> T = {})" by (simp add: a4)
        have as4: "\<forall>S\<in>?U. (S \<noteq>{})" using prettybig by force
have alm: "card (\<Union>?U) = (card ?U) * (card {B. \<exists>S\<in>?U. (B \<in> S)}) / card ?U" 
  proof -
    have "card ?U = 0 \<or> card ?U > 0" by auto
    moreover 
    {assume "card ?U = 0"
      hence "?U = {}" using as1 by simp
      hence "card (\<Union>?U) = (card ?U) * (card {B. \<exists>S\<in>?U. (B \<in> S)}) / card ?U" by fastforce}    
    moreover 
    {assume "card ?U > 0"
      hence alg1: "(card ?U) * (card {B. \<exists>S\<in>?U. (B \<in> S)}) / card ?U = card {B. \<exists>S\<in>?U. (B \<in> S)}" by force
      from as1 as2 as3 as4 have "card (\<Union>?U) = card {B. \<exists>S\<in>?U. (B \<in> S)}" by (metis Union_eq)
      hence "card (\<Union>?U) = (card ?U) * (card {B. \<exists>S\<in>?U. (B \<in> S)}) / card ?U" using alg1 by presburger}
    ultimately show ?thesis by linarith qed
  have "{B. \<exists>S\<in>?U. (B \<in> S)} =  {B. being B \<and>  preposthuman B \<and> (\<exists>C. (B \<in> C \<and> civilization C \<and> (C runs N sims)))}"
*)  
     
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
  

text "We will introduce the fraction of simulated beings vs. real beings"
abbreviation fsim:: real
  where "fsim \<equiv> card {B. simulated B} / card {B. preposthuman B}"
    
lemma fsimmi: "fsim \<ge> (N * s * H\<^sub>s) / (N*s*H\<^sub>s + n * H\<^sub>n + s * H\<^sub>s)"
  sorry (*see above*)
    
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
  hence a4: "1 / 99 - 1/ N <  n / (s * 1000000)" by fastforce 
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
shows "card {C. civilization C \<and> \<not> posthumansoc C} / card {C. civilization C} \<ge> ((99::real)/100)" 
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
  hence ine: "a / (s + a + b) \<ge> a / (s + a + 99 * s)" using on by (simp add: add_gr_0 frac_le)
  have "9901 * s < a" using fsimb flow Nhuge blow by blast
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
  hence "a / (s + a + 99 * s) \<ge> a / (s + 9901 * s + 99 * s)"
  (*Vampire says: "remote_vampire": The prover derived "False" from "Hsnot0", "OnlyPostSim", "all_not_in_conv", "card.empty", "citizenship", "div_0", "empty_Collect_eq", "leD", "less_numeral_extra(3)", "of_nat_0", and "prettybig", which could be due to inconsistent axioms (including "sorry"s) or to a bug in Sledgehammer*)  
 (*Somehow there is an inconsistency; but I don\<acute>t see it; This needs to be fixed*)   
 
  
end
  