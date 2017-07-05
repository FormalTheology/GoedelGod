theory bostromprob
  
  imports Complex_Main Appendix
    
begin

  
text "For the formalization of 9the argument we will introduce the predicates WeIn and  PIn. PIn X is to be interpreted
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