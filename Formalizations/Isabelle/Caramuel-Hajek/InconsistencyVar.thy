theory InconsistencyVar
  
imports Main "../QML_S5_var"
    
begin
text {*
This is a quick demonstration that if using the QML_S5_var.thy which states that 
"\<forall>w. \<exists>x. eiw x w" Caramuels Assumptions become inconsistent.*}
  
consts G:: "\<mu> \<Rightarrow> \<sigma>" (*Property of being godlike*)  
consts P:: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  (*(2. order) property of being positive*)
abbreviation E :: "\<mu> \<Rightarrow> \<sigma>" ("\<^bold>\<forall>\<^sup>E") where "E \<equiv> eiw" (*For consistency with the paper\<acute>s notation*)


theorem Inconsistent: (*Uses the assumptions by Hajek\<acute>s Caramuel*)
assumes  *: "\<And>u.\<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(G u \<^bold>\<and> E u) \<rfloor>"
and Ax4: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<forall>x. (\<^bold>\<not> E x  )) \<rfloor>" 
shows "A \<and> \<not>A" 
proof -
  have False using Ax4 nonempty by blast
  thus ?thesis by blast
qed
end
  
