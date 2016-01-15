theory QML imports Main 
begin
section {* An Embedding of QML in HOL *}

  typedecl i                                      -- "the type for possible worlds" 
  typedecl \<mu>                                      -- "the type for individuals"      
  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)     -- "accessibility relation r"   

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<not> _" [53] 52) where "\<^bold>\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<and>" 51) where "\<phi> \<^bold>\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<or>" 50) where "\<phi> \<^bold>\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<rightarrow>" 49) where "\<phi> \<^bold>\<rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "\<^bold>\<equiv>" 48) where "\<phi> \<^bold>\<equiv> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<forall>") where "\<^bold>\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"
  abbreviation mforallB :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (binder "\<^bold>\<forall>" [9] 9)  where "\<^bold>\<forall> x. \<phi> x \<equiv> \<^bold>\<forall> \<phi>"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<exists>") where "\<^bold>\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mexistsB :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (binder "\<^bold>\<exists>" [9] 9)  where "\<^bold>\<exists> x. \<phi> x \<equiv> \<^bold>\<exists> \<phi>"   
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<box>") where "\<^bold>\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<^bold>\<diamond>") where "\<^bold>\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>\<^bold>_\<rfloor>") where "\<lfloor>\<^bold>p\<rfloor> \<equiv> \<forall>w. p w" 
end
