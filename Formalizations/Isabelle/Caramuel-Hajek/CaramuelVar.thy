theory CaramuelVar
  
imports Main "../QML_var"
begin
  
consts G:: "\<mu> \<Rightarrow> \<sigma>" (*Property of being godlike*)  
abbreviation E:: "\<mu> \<Rightarrow> \<sigma>" where "E \<equiv> eiw"(*"actual existence"*)
consts P:: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  (*(2. order) property of being positive*)

(*Axiomatization of Caramuel\<acute>s Argument.
Note that axiom 1 is not even needed for the inconsistency even in K.*)
(*axiomatization where  *: "\<And>u.\<lfloor>(G u) \<^bold>\<rightarrow> \<^bold>\<box>(G u \<^bold>\<and> E u) \<rfloor>" *)
axiomatization where  Ax4: "\<lfloor>\<^bold>\<diamond> (\<^bold>\<forall>x. (\<^bold>\<not> (E x)  )) \<rfloor>"


(*Modal Logic K: *)
lemma False using Ax4 nonempty by blast  
(*Why the inconsistency? Let w be be a fixed but arbitrary world. By Ax4 there exists a world where:
there is no x so that E x. Axiom nonempty states that there is. Therefore False.
Note that we only need the definitions of the diamond operator here to conclude False.*)
end