(*<*) 
theory AndersonSimplification_var
imports Main "../QML_S5_var"

begin
(*>*)

section {* Anderson's Simplification *}   
  
  text {* Anderson 1990 claims (in page 7) that axioms A1, A2 and A4 are provable,
          as long as "Positive" is defined in a certain way based on a new constant "Defective".
          These claims are confirmed here.
          However, proving A4 requires symmetry and transitivity of the accessibility relation *} 

  consts Defective :: "\<mu> \<Rightarrow> \<sigma>" 
  
  definition P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" where
  "P \<Phi> \<equiv> (\<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex. ((\<^bold>\<not> (\<Phi>(x))) \<^bold>\<rightarrow> Defective(x)))) \<^bold>\<and> (\<^bold>\<not> (\<^bold>\<box>(\<^bold>\<forall>\<^sup>Ex.( (\<Phi>(x)) \<^bold>\<rightarrow> Defective(x))) ))"

  theorem A1:  "\<lfloor>\<^bold>\<forall>\<Phi>. (((P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<not> (P (\<^sup>\<not> \<Phi>)) )  )\<rfloor>"
  by (metis P_def)

  theorem A2:  "\<lfloor>\<^bold>\<forall>\<Phi>.( \<^bold>\<forall>\<Psi>. (( (P \<Phi>) \<^bold>\<and> \<^bold>\<box> (\<^bold>\<forall>\<^sup>Ex. ((\<Phi> x) \<^bold>\<rightarrow> (\<Psi> x) ))) \<^bold>\<rightarrow> (P \<Psi>)))\<rfloor>"
  by (metis P_def)

  theorem  A4:  "\<lfloor>\<^bold>\<forall>\<Phi>.( (P \<Phi>) \<^bold>\<rightarrow> \<^bold>\<box> (P \<Phi>))\<rfloor>"
  by (smt P_def sym trans)

(*<*) 
end
(*>*) 
