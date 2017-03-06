theory Hajek2008
  
imports Main "../QML_S5"
    
begin


(*Now the actual arguments from Hájek\<acute>s paper*)  
consts G:: "\<mu> \<Rightarrow> \<sigma>" (*Property of being godlike*)  
consts E:: "\<mu> \<Rightarrow> \<sigma>" (*"actual existence"*)
consts P:: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  (*(2. order) property of being positive*)

abbreviation actualexistence::  "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder "\<exists>\<^sup>E"[8]9)
where "\<exists>\<^sup>Ex. \<phi>(x)  \<equiv> \<^bold>\<exists>x. (  \<phi>( x)  \<^bold>\<and> (E x) )"
abbreviation actualforall::  "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder "\<forall>\<^sup>E"[8]9) (*Not actually used anywhere*)
where "\<forall>\<^sup>Ex. \<phi>(x)  \<equiv> \<^bold>\<forall>x. (  \<phi>(x ) \<^bold>\<rightarrow> E x )"

  

theorem Argument1: (*Gödeloid *argument FOR the existence of god*)
assumes Ax1: "\<And>u. \<lfloor>G u \<^bold>\<leftrightarrow> (  \<^bold>\<forall> Y.(  P Y  \<^bold>\<rightarrow>  \<^bold>\<box>(Y u) )) \<rfloor>"  
and Ax2a: "\<lfloor>P G\<rfloor>"
and Ax2b:"\<lfloor>P E\<rfloor>"
and Ax3: "\<lfloor>\<^bold>\<forall>Y. (P Y \<^bold>\<rightarrow> \<^bold>\<diamond> (\<exists>\<^sup>E u. Y u)) \<rfloor>"
shows "\<lfloor>\<^bold>\<box> (\<exists>\<^sup>E u. G u)\<rfloor>"
proof -
(*Nitpick proves consistency of assumptions; Uncomment to confirm  
  have True nitpick [satisfy, user_axioms, expect = genuine] *)
have lemma1a: "\<And>u. \<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(G u)\<rfloor>"
  proof -
  have "\<And>u. \<lfloor>G u \<^bold>\<rightarrow> (  \<^bold>\<forall> Y.(  P Y  \<^bold>\<rightarrow>  \<^bold>\<box>(Y u) )) \<rfloor>" using Ax1 by auto
  hence "\<And>u. \<lfloor>G u \<^bold>\<rightarrow>  P G  \<^bold>\<rightarrow>  \<^bold>\<box>(G u)  \<rfloor>" by blast
  thus  "\<And>u. \<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(G u)\<rfloor>" using Ax2a by blast qed
 have lemma1b: "\<And>u.\<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(E u)\<rfloor>"
  proof -
  have "\<And>u.\<lfloor>G u \<^bold>\<rightarrow> (  \<^bold>\<forall> Y.(  P Y  \<^bold>\<rightarrow>  \<^bold>\<box>(Y u) )) \<rfloor>" using Ax1 by auto
  hence "\<And>u.\<lfloor>G u \<^bold>\<rightarrow>  P E  \<^bold>\<rightarrow>  \<^bold>\<box>(E u)  \<rfloor>" by blast
  thus  "\<And>u.\<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(E u)\<rfloor>"  using Ax2b by blast qed
have lemma1c:  "\<And>u.\<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(G u \<^bold>\<and> E u) \<rfloor>" using lemma1a lemma1b by blast
have lemma2: "\<lfloor>\<^bold>\<diamond>( \<exists>\<^sup>E u. G u ) \<^bold>\<rightarrow> \<^bold>\<box>(\<exists>\<^sup>E u. G u) \<rfloor>"
  proof -
    have "\<lfloor>(\<^bold>\<exists>u. G u) \<^bold>\<rightarrow> ( \<^bold>\<exists>u. \<^bold>\<box>(G u \<^bold>\<and> E u)) \<rfloor>"
    proof - (*provers fail; done manually*)
      {fix w::i (*fix a world*)
      {assume "( \<^bold>\<exists> u. G u) w"
      hence "\<exists> u. G u w" by blast
      from this obtain x where "G x w" by blast
      hence "G x w" by simp
      from lemma1c have "((G x) w \<longrightarrow> (\<^bold>\<box>(G x \<^bold>\<and> E x)) w)" by blast
      hence "( \<^bold>\<box>(G x \<^bold>\<and> E x)) w" using \<open>G x w\<close> by blast
      hence " (\<^bold>\<exists>u. \<^bold>\<box>(G u \<^bold>\<and> E u)) w"  by blast} 
      hence "(\<^bold>\<exists> u. (G u)) w  \<longrightarrow>  (\<^bold>\<exists>u. \<^bold>\<box>(G u \<^bold>\<and> E u)) w" by blast}
      thus ?thesis by blast qed  
    hence "\<lfloor>(\<^bold>\<exists>u. G u) \<^bold>\<rightarrow> \<^bold>\<box> ( \<^bold>\<exists>u.(G u \<^bold>\<and> E u)) \<rfloor>" by blast
    hence "\<lfloor>(\<^bold>\<exists>u. G u) \<^bold>\<rightarrow>  \<^bold>\<box> ( \<exists>\<^sup>E u. G u)\<rfloor>" by blast
    hence "\<lfloor>(\<exists>\<^sup>E u. G u) \<^bold>\<rightarrow>  \<^bold>\<box> ( \<exists>\<^sup>E u. G u)\<rfloor>" by blast
    thus ?thesis by blast qed
thus ?thesis using Ax2a Ax3 by blast
qed      

theorem Argument2: (*Caramueloid argument AGAINST the existence of god*)
assumes  *: "\<And>u.\<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(G u \<^bold>\<and> E u) \<rfloor>" (*follows from Ax1a/b and Ax2; see above*)
and Ax4: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<forall>x. (\<^bold>\<not> E x  )) \<rfloor>"
shows "\<lfloor>\<^bold>\<box> ( \<^bold>\<not>(\<exists>\<^sup>E u. G u))\<rfloor>" 
proof -
(*Nitpick proves consistency of assumptions; Uncomment to confir)
  have True nitpick [satisfy, user_axioms, expect = genuine]  *)
  have "\<lfloor>\<^bold>\<not> (\<^bold>\<exists> x. G x)\<rfloor>" using "*" Ax4 by blast 
  hence  "\<lfloor>\<^bold>\<not> (\<^bold>\<exists> x. (G x \<^bold>\<and> E x))\<rfloor>" by simp
  thus ?thesis by blast
qed
end
  
