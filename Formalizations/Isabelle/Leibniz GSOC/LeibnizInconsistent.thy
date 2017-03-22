theory LeibnizInconsistent
  
  imports Main 
    
begin
typedecl \<mu> (*Things in the World*)
  
consts moving :: "\<mu> \<Rightarrow> bool"
consts movesxy :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> bool" (infixr "moves"52) (*Is 52 good?*)
abbreviation movesx :: "\<mu> \<Rightarrow> bool" ("is-mover") where "(is-mover x) \<equiv> (\<exists>y. (x moves y))"  
consts is_moved :: "\<mu> \<Rightarrow> bool"
consts body :: "\<mu> \<Rightarrow> bool"
abbreviation incorporeal :: "\<mu> \<Rightarrow> bool" where "incorporeal x \<equiv> \<not> body x"
consts partxy :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> bool" (infixr "is-part-of"52)
 
    
abbreviation Substance :: "\<mu> \<Rightarrow> bool" where "Substance x \<equiv> (\<exists>y. x moves y ) \<or> is_moved x"
abbreviation infinitePower :: "\<mu> \<Rightarrow> bool" where 
"infinitePower x \<equiv> \<exists>(S::\<mu> set). (infinite S  \<and> (\<forall>y. ((y \<in> S) \<longrightarrow>  x moves y)))"   
abbreviation God :: "\<mu> \<Rightarrow> bool" where "God x \<equiv> incorporeal x \<and> Substance x \<and> infinitePower x"
  
axiomatization where Postulate_a: "((P y) \<and> x is-part-of y) \<longrightarrow> P x" (*The important Parts of Leibniz\<acute> mereology*)  
axiomatization where Postulate_b: "\<And>(S:: \<mu> set). (\<exists>C. (\<forall>x. (x \<in> S \<longrightarrow> (x is-part-of C))))" (*Every Set can be made into an object*)
axiomatization where Axiom1: "(is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
axiomatization where Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
axiomatization where Axiom3: "(\<forall>x. (x is-part-of y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y"
axiomatization where Axiom4: "\<forall>x. ((body x) \<longrightarrow> (\<exists>(S::\<mu> set). (infinite S \<and> (\<forall>y. (y \<in> S)\<longrightarrow>(y is-part-of x)))))" 
axiomatization where Observation: "\<exists>x. (body x \<and> moving x)"
(*axiomatization where Add1: "x moves y \<longrightarrow> moving x" (*Not one of Leibniz Axioms! See comment below*)
*)axiomatization where Add2: "\<not> x moves x"  (*Not one of Leibniz Axioms! See comment below*)
  
(*
There are two things that are added to the argument. The two postulates and the additional axioms Add1 and Add2.
The postulates seem to correspond broadly to Leibniz Postulate. It could be that weaker versions suffice 
for the proof.

Why are Add1 and Add2 necessary? Assume Add1 doesn\<acute>t hold. Then there could be a body (therefore not god)
that moves every other body but is itself static (not moving). This is consistent as one (but not nitpick bc. of the infinity in the axioms) 
can easily verify. Is Add1 a plausible addition to Leibniz Axioms? I think so. If the notion of bodies is understood
in a broadly physicalistic way and a Newtonian Physics is assumed then Add1 is the most plausible interpretation.
It seems to be consistent with what Leibniz himself might have subscribed to.

Assume Add2 doesn\<acute>t hold. Then for example the collection of all moving things (C in Leibniz\<acute> argument) could simply move itself.
No need for any god arises. Again this is consistent with all the axioms.

Therefore both Add1 and Add2 seem good additions for Leibniz\<acute> argument.
*)
(*However, with the Addition of Add2 the axiom set becomes inconsistent.
Sledgehammer is a bit slow to prove this, so here is a small but not fully automated proof of the 
inconsistency*)

lemma False
proof- 
from Observation have  "\<exists>A. (body A \<and> moving A)" by simp
then obtain A where "(body A \<and> moving A)" by auto
hence "\<exists>x. (x moves A)" using Axiom1 by (simp add: Axiom2)
  then obtain mover where "mover moves A" by auto
have "body mover" by (meson Add2 Postulate_a Postulate_b \<open>mover moves A\<close> iso_tuple_UNIV_I)      
have "\<forall>x. x \<in> {y. is_moved y} \<longrightarrow> x is-part-of C"  by (meson Postulate_a Postulate_b iso_tuple_UNIV_I)      
  thus ?thesis by (meson Add2 Postulate_a Postulate_b UNIV_I \<open>mover moves A\<close>)
 qed    

(*Like with all formal proofs that result from natural language Arguments it is not evident whether 
the original argument is also inconsistent or whether this is an artifact of the formal system.
At least as long as there is no proof of inconsistency that can be translated back to
natural language.*)  