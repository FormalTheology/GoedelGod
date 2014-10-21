theory QML_var
imports Main QML

begin
section {* Varying Domains *}

text {* Technically, varying domains are encoded with the help of an 
        existence relation expressing which individuals actually exist in each world. *}

  consts eiw :: "\<mu> \<Rightarrow> i \<Rightarrow> bool"
  axiomatization where nonempty: "\<forall>w. \<exists>x. eiw x w"


text {* Actualistic quantifiers are quantifiers guarded by the existence relation. *}

  abbreviation mforalle :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>e") where "\<forall>e \<Phi> \<equiv> (\<lambda>w. \<forall>x. (eiw x w) \<longrightarrow> (\<Phi> x w))"     
  abbreviation mexistse :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>e") where "\<exists>e \<Phi> \<equiv> (\<lambda>w. \<exists>x. (eiw x w) \<and> \<Phi> x w)" 
  
end
