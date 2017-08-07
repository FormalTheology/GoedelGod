theory Leibniz
  
  imports Main 
    
begin
typedecl \<mu> (*Things in the World*)
  
consts moving :: "\<mu> \<Rightarrow> bool"
consts moves :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> bool" (infixr "moves"52) 
abbreviation is_mover :: "\<mu> \<Rightarrow> bool"  where "(is_mover x) \<equiv> (\<exists>y. (x moves y))"  
consts is_moved :: "\<mu> \<Rightarrow> bool"
consts body :: "\<mu> \<Rightarrow> bool"
abbreviation incorporeal :: "\<mu> \<Rightarrow> bool" where "incorporeal x \<equiv> \<not> body x"
consts is_part_of :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> bool" (infixr "ispartof"52)
consts has_infinite_parts :: "\<mu> \<Rightarrow> bool" 
consts moves_the_infinite :: "\<mu> \<Rightarrow> bool"  

abbreviation infinitePower :: "\<mu> \<Rightarrow> bool" where 
"infinitePower x \<equiv>  moves_the_infinite x"
  
abbreviation Substance :: "\<mu> \<Rightarrow> bool" where "Substance x \<equiv> (\<exists>y. x moves y ) \<or> is_moved x"

abbreviation God :: "\<mu> \<Rightarrow> bool" where "God x \<equiv> incorporeal x \<and> Substance x \<and> infinitePower x"
  
text "The following axiom seems to be a reasonable interpretation of Leibniz\<acute> notion of infinity."

axiomatization where inf: "has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  

text "Leibniz\<acute> postulate is not very precise.
\<acute>The concept of parts is this: given a plurality of beings all of which have something in common [...]
one name is thought of which takes the place of all its part in our reasoning[...]. This is calles the Whole.\<acute>
We interpret this as: If a property is instantiated then there is something such that every 
thing that instantiates this property is a part of said thing/the Whole."
axiomatization where Postulate_a: "(\<exists>x. P x) \<Longrightarrow> (\<exists>t. (\<forall>x.(P x \<longleftrightarrow> (x ispartof t))))"

text "Leibniz Axioms are interpreted in a straight forward manner."
  
axiomatization where Axiom1: "(is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
axiomatization where Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
axiomatization where Axiom3: "(\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
axiomatization where Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
axiomatization where Observation: "\<exists>x. (body x \<and> moving x)"


text "However, these are not enough to get to the conclusion that Leibniz wants."
  
lemma "\<exists>x. God x" nitpick[user_axioms, verbose] (*Nitpick finds a counterexample*)
  oops
    
  text "To model Leibniz\<acute> argument as closely as possible (and to make the argument sound)
a couple of new axioms are intoduced that are plausible in the context of Leibniz argument."
    
  text "If we suppose a broadly Newtonian physics then it seems plausible that if a body is a mover,
then it is moving itself. This does not preclude the notion of an unmoved mover, but whatever it is
it is not a body."    
axiomatization where Add1: "body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
  
text "We also need to postulate that bodies don\<acute>t move themselves. Since if that were the case
every body could just move itself and there would be no need for god."
axiomatization where Add2: "body x \<Longrightarrow> \<not> x moves x" (*With Add3 we could also use the stronger
axiom that everything is a part of itself*)

text "It also stands to reason that no part of a Whole moves the entire whole since that
would probably mean that something would move itself. It is not entirely obvious that this should
indeed be an axiom. It seems on the face of it correct to say that an engine moves a car while being
part of it."
axiomatization where Add3: "x ispartof y \<Longrightarrow> \<not> x moves y"
  
text "Lastly, if something is \<acute>made out of bodies\<acute> it is itself a body. Again, with a broadly 
Newtonian physics in the background this seems unproblematic."  
axiomatization where Add4: "(\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
  
text "We can also derive a lemma that seems to correspond well to Leibniz argument in the \<acute>postulate\<acute> part
that there is a Whole that comprises all (moving) bodies."  
lemma theWhole: "\<exists>w. (\<forall>(x::\<mu>). (body x \<longrightarrow> moving x \<longrightarrow> x ispartof w))" using Postulate_a Observation by meson 

text "Next we derive the conclusion that god exists. The formal argument tries to mirror Leibniz\<acute>
natural language argument. This isn\<acute>t always possible so in the second half a structure was chosen
that still tries to capture the spirit of the argument."    

lemma God: "\<exists>x. God x"
proof -
  from Observation have  "\<exists>A. (body A \<and> moving A)" by simp
then obtain A where obtA: "(body A \<and> moving A)" by auto
hence "\<exists>x. (x moves A)" using Axiom1 by (simp add: Axiom2)
then obtain mover where obtmover: "mover moves A" by auto
  have "incorporeal mover \<or>  body mover" by simp
  {assume "incorporeal mover"
  have "infinitePower mover" using Axiom4 \<open>mover moves A\<close> inf obtA by blast
  have "Substance mover" using \<open>(mover moves A)\<close> by auto
  hence "God mover" by (simp add: \<open>incorporeal mover\<close> \<open>infinitePower mover\<close>)
  hence "\<exists>x. God x" by auto}   
  moreover
  {assume bm: "body mover"
    hence "is_moved mover" using Add1 Axiom2 \<open>mover moves A\<close> by auto
(*Note that this step needs something like Add1 even in natural language.*)
{assume "\<not> (\<exists>x. (God x))"
  have "\<exists>C. (\<forall>x. (is_moved x \<and> body x ) \<longleftrightarrow> x ispartof C)"
  proof -
    from obtmover bm have "\<exists>x. (\<lambda>l.(body l \<and> is_moved l)) x" using \<open>is_moved mover\<close> by auto
    hence "\<exists>C. (\<forall>x. (\<lambda>l.(body l \<and> is_moved l)) x \<longleftrightarrow> x ispartof C)" using Postulate_a by simp
    then obtain C where obtC1: "(\<forall>x. (\<lambda>l.(body l \<and> is_moved l)) x \<longleftrightarrow> x ispartof C)" by auto
    hence "(\<forall>x. (is_moved x \<and> body x ) \<longleftrightarrow> x ispartof C)" by auto
    thus ?thesis by auto qed    
   then obtain C where obtC: " (\<forall>x. (is_moved x \<and> body x ) \<longleftrightarrow> x ispartof C)" by blast
   have "is_moved C" using Axiom3 using \<open>\<forall>x. (is_moved x \<and> body x) = x ispartof C\<close> by blast
   hence "\<exists>G. G moves C" using Axiom1 by simp
   from this obtain G where "G moves C" by auto
   have "incorporeal G"  using Add1 Add3 Axiom2 \<open>G moves C\<close> \<open>\<forall>x. (is_moved x \<and> body x) = x ispartof C\<close> by blast 
   have "Substance G" using \<open>G moves C\<close> using Add1 Add3 Axiom2 \<open>\<forall>x. (is_moved x \<and> body x) = x ispartof C\<close> by blast
   have "body C" using Add4 obtC by fast
   hence "God G" using Axiom4 \<open>body C\<close>  \<open>Substance G\<close>  \<open>incorporeal G\<close>  \<open>G moves C\<close> inf by blast
   hence "False" using \<open>\<nexists>x. God x\<close> by blast}
   hence "\<exists>x. (God x)" by blast}
   ultimately show "\<exists>x. (God x)" by auto
qed

end