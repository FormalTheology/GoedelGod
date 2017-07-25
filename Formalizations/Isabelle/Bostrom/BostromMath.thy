theory BostromMath

  imports Complex_Main
    
begin

section "Useful lemmas for Bostrom\<acute>s arguments"  
   
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

end  