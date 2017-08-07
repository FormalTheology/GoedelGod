theory LeibnizFurther

  imports Main
    
begin

text "Because we don\<acute>t want the axioms to hold in this file Leibniz.thy is not imported.
Instead we define the constants once more."

typedecl \<mu> (*Things in the World*)
  
consts moving :: "\<mu> \<Rightarrow> bool"
consts moves :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> bool" (infix "moves"52) 
abbreviation is_mover :: "\<mu> \<Rightarrow> bool"  where "(is_mover x) \<equiv> (\<exists>y. (x moves y))"  
consts is_moved :: "\<mu> \<Rightarrow> bool"
consts body :: "\<mu> \<Rightarrow> bool"
abbreviation incorporeal :: "\<mu> \<Rightarrow> bool" where "incorporeal x \<equiv> \<not> body x"
consts is_part_of :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> bool" (infix "ispartof"52)
consts has_infinite_parts :: "\<mu> \<Rightarrow> bool" 
consts moves_the_infinite :: "\<mu> \<Rightarrow> bool"  

abbreviation infinitePower :: "\<mu> \<Rightarrow> bool" where 
"infinitePower x \<equiv>  moves_the_infinite x"
  
abbreviation Substance :: "\<mu> \<Rightarrow> bool" where "Substance x \<equiv> (\<exists>y. x moves y ) \<or> is_moved x"

abbreviation God :: "\<mu> \<Rightarrow> bool" where "God x \<equiv> incorporeal x \<and> Substance x \<and> infinitePower x"
  
  
section "Some reasons for accepting Add2"
text "Without Add2 it is consistent with all other axioms that every moving body moves itself.
Thus, there is no need for god."
  
lemma Cons:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and AntiAdd2: "\<And>x. body x \<Longrightarrow>  x moves x" 
and nogod: "\<not> (\<exists>x. God x)"
shows True nitpick[satisfy, verbose, timeout=300] (*Nitpick finds a model*)  
  oops
      
  
section "Consistency"

lemma Cons:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows True nitpick[satisfy, verbose, timeout=300] (*Nitpick finds NO model*)  
  oops
    
lemma Inc1:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows False sledgehammer[verbose, timeout = 300] (*local provers can\<acute>t prove false*)
  oops

lemma Inc1:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows False sledgehammer[remote_leo2 remote_satallax remote_vampire, remote_e, verbose]    
(*External provers can\<acute>t prove false*)
  oops
    
  text "Consistency is an open question."
    
    
section "Are all axioms necessary?"
  
lemma WOinf:
assumes Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample; but there is one of course,
namely that movestheinfinite is always false therefore nothing has is and therefore the is no god.*)
  oops  


lemma WOPosta:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds a counterexample*)
 oops
      
lemma WOAx1:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds a counterexample*)
 oops
   
lemma WOAx2:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds a counterexample*)
  oops
    
lemma WOAx3:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops    

lemma WOAx4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample, but again there clearly is one,
namely that nothing has infinite parts and only if something moves a thing with infinite parts it
moves the infinite, therefore nothing does therefore no god.*)
 oops   
   

lemma WOObs:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds a counterexample*)
 oops         

lemma WOAdd1:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
  oops
    
lemma WOAdd2:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops    

lemma WOAdd3:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds no counterexample*)
 oops   

lemma WOAdd4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds no counterexample*)
 oops
             
 text "Possible redundancies are Axiom3, and all Add1-Add4."   

 text "Since sledgehammer isn\<acute>t able to prove the argument with only a few steps, it is not
a trivial task to find out what a minimal set of axioms is. We can however See if we find a countermodel
for combinations of those 5 axioms."

subsection "Without Axiom 3"   
   lemma WOAx3Add1:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops    

lemma WOAx3Add2:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops  

lemma WOAx3Add3:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops  

lemma WOAx3Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops  

lemma WOAx3Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops     
   
 text "We can leave out any of the additional premises and Ax3 and nitpick still does not find a 
countermodel." 
   
subsection "Without Add1"
lemma WOAdd1Add2:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
  oops

lemma WOAdd1Add3:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
  oops
    
lemma WOAdd1Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
  oops
    
  text "We find the same phenomenon for Add1."

  subsection "Without Add2"    
    
lemma WOAdd2Add3:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds a counterexample*)
 oops      

lemma WOAdd2Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops     

text "For the argument to succeed we need either Add2 or Add3"   

section "Without Add3"

lemma WOAdd3Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds no counterexample*)
 oops   
  
subsubsection "Without both Axiom 3 and Add1"   
 lemma WOAx3Add1Add2:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
   oops
     
 lemma WOAx3Add1Add3:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add4: "\<And>y. (\<forall>x. x ispartof y \<longrightarrow> body x) \<Longrightarrow> body y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops    

 lemma WOAx3Add1Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops    
   
subsubsection "Without both Axiom3 and Add2"

text "We already know that we need Add3 since we don\<acute>t have Add2"
  
lemma WOAx3Add2Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
  oops
    
subsubsection "Without both Axiom 3 and Add3"    

lemma WOAx3Add3Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add1: "\<And>x y. body x \<Longrightarrow> (x moves y \<longrightarrow> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
 oops  

text "This might be prima facie evidence that Axiom 3 is superfluous."

subsubsection "Without both Add1 and Add2"

text "We already know that we need Add3"
  
lemma WOAdd1Add2Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add3: "\<And>x y. x ispartof y \<Longrightarrow> \<not> x moves y"
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
  oops
  
subsubsection "Without bot Add1 and Add3"
    
text "We already know we need Add2"
  
lemma WOAdd1Add3Add4:
assumes inf: "\<And>y x. has_infinite_parts y \<Longrightarrow> x moves y \<Longrightarrow> moves_the_infinite x"  
and  Postulate_a: "\<And>P. (\<exists>x. P x) \<Longrightarrow> (\<exists>w. (\<forall>x.(P x \<longleftrightarrow> (x ispartof w))))"
and  Axiom1: " \<And>x. (is_moved(x)) \<longrightarrow> ( \<exists>y. (y moves x))"  
and Axiom2: "\<forall>x. (moving x \<and> body x) \<longrightarrow> is_moved x"
and Axiom3: "\<And>y. (\<forall>x. (x ispartof y \<longrightarrow> is_moved x)) \<longrightarrow> is_moved y" 
and  Axiom4: "\<forall>x. ((body x) \<longrightarrow> (has_infinite_parts x))" 
and Observation: "\<exists>x. (body x \<and> moving x)"
and Add2: "\<And>x. body x \<Longrightarrow> \<not> x moves x" 
shows "\<exists>x. God x" nitpick[verbose] (*Nitpick finds NO counterexample*)
  oops  
    
  text "The results are inconclusive. Axiom 3 and Add4 might not be needed at all, at least one of
Add2 and Add3 is needed."
    
    
end