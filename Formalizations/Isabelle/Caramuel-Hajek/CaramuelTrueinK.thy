theory CaramuelTrueinK
  
imports Main "../QML"
begin
  
consts G:: "\<mu> \<Rightarrow> \<sigma>" (*Property of being godlike*)  
consts E:: "\<mu> \<Rightarrow> \<sigma>" (*"actual existence"*)
consts P:: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  (*(2. order) property of being positive*)

abbreviation actualexistence::  "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder "\<exists>\<^sup>E"[8]9)
where "\<exists>\<^sup>Ex. \<phi>(x)  \<equiv> \<^bold>\<exists>x. (  \<phi>( x)  \<^bold>\<and> (E x) )"
abbreviation actualforall::  "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder "\<forall>\<^sup>E"[8]9) (*Not actually used anywhere*)
  where "\<forall>\<^sup>Ex. \<phi>(x)  \<equiv> \<^bold>\<forall>x. (  \<phi>(x ) \<^bold>\<rightarrow> E x )"

(*Axiomatization of Caramuel\<acute>s Argument.
Note that axiom 1 is not even needed for the Argument to succeed even in K.*)
(*axiomatization where  *: "\<And>u.\<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(G u \<^bold>\<and> E u) \<rfloor>" *)
axiomatization where  Ax4: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<forall>x. (\<^bold>\<not> (E x)  )) \<rfloor>"


(*Modal Logic K: *)
lemma "\<lfloor>\<^bold>\<not>(\<^bold>\<box> (\<exists>\<^sup>E u. G u))\<rfloor>" using Ax4 by blast  

  
lemma True nitpick[satisfy, user_axioms, expect = genuine]
oops (*Ax4 is consistent*)
    

  
end
  