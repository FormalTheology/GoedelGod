theory Hajek2008
  
imports Main
    
begin
(*Using the semantic embedding of S5 by Benzmüller and Woltzenlogel-Paleo;
Can be deleted if importing QML.thy*)
typedecl i -- "type for possible worlds" 
typedecl \<mu> -- "type for individuals"      
type_synonym \<sigma> = "(i\<Rightarrow>bool)"

consts r :: "i\<Rightarrow>i\<Rightarrow>bool" (infixr "r" 70)    -- "accessibility relation r"   


abbreviation mnot   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53)
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
abbreviation mnegpred :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>(\<mu>\<Rightarrow>\<sigma>)" ("\<^sup>\<not>_"[52]53) 
  where "\<^sup>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>\<Phi>(x)(w)"   
abbreviation mand   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51)
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
abbreviation mor    :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50)
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
abbreviation mimp   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"
abbreviation mequ   :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<leftrightarrow>"48)
  where "\<phi>\<^bold>\<leftrightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"  
abbreviation mforall   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>")      
  where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
abbreviation mforallB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9)
  where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
abbreviation mexists   :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
abbreviation mexistsB  :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9)
  where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
abbreviation mbox   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>_"[52]53)
  where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w.\<forall>v. w r v \<longrightarrow> \<phi>(v)"
abbreviation mdia   :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>_"[52]53)
  where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w.\<exists>v. w r v \<and> \<phi>(v)"  
  
abbreviation valid :: "\<sigma>\<Rightarrow>bool" ("\<lfloor>_\<rfloor>"[8]109)
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"

axiomatization  where S5: "\<forall>x y. x r y"


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
    thus ?thesis using S5 by blast qed
thus ?thesis using Ax2a Ax3 by blast
qed      

theorem Argument2: (*Caramueloid argument AGAINST the existence of god*)
assumes  *: "\<And>u.\<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(G u \<^bold>\<and> E u) \<rfloor>" (*follows from Ax1a/b and Ax2; see above*)
and Ax4: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<forall>x. (\<^bold>\<not> E x  )) \<rfloor>"
shows "\<lfloor>\<^bold>\<not>\<^bold>\<box> (\<exists>\<^sup>E u. G u)\<rfloor>" 
proof -
  have "\<lfloor>\<^bold>\<not> (\<^bold>\<exists> x. G x)\<rfloor>" using "*" Ax4 by blast 
  hence  "\<lfloor>\<^bold>\<not> (\<^bold>\<exists> x. (G x \<^bold>\<and> E x))\<rfloor>" by simp
  thus ?thesis using S5 by blast
qed
end
  
