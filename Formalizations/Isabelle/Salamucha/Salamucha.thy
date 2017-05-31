theory Salamucha

imports Main

begin
  
section "Types and Definitions"  
typedecl a (*things and stuff in the world*) 
consts R:: "a \<Rightarrow> a \<Rightarrow> bool" (*(infixr "R"52)*) (*_ moves _*)
consts f :: "a \<Rightarrow> bool" (*is in motion*)
consts partof :: "a \<Rightarrow> a \<Rightarrow> bool" (infixr "M"52) (*_ is a proper part of _*)  
consts aspactu :: "a \<Rightarrow> 'a \<Rightarrow> a \<Rightarrow> bool" ("_A\<^sub>_ _")
consts asppot :: "a \<Rightarrow> 'a \<Rightarrow> a \<Rightarrow> bool" ("_ P\<^sub>_ _") 
consts body:: "a \<Rightarrow> bool" ("C")
consts duration :: "'a \<Rightarrow> a \<Rightarrow> bool" ("_ F _") (*not entirely sure if we need a "time type" here; I don\<acute>t think it will change anything*)  
consts finitetime :: "'a \<Rightarrow> bool" ("H") 
  
  
abbreviation CC:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" (*Salamucha has C\<acute>R*)
  where "CC r \<equiv> {a. \<exists>t. ((r a t) \<or> (r t a))}"

abbreviation irreflexive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "irreflexive r \<equiv> (\<forall>x. \<not> (r x x))"   

abbreviation transitive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transitive r \<equiv> (\<forall>x y z. ((r x y) \<and> (r y z) \<longrightarrow> ( r x z)))"   

abbreviation connected :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "connected r \<equiv> \<forall>x y. ((x \<in> (CC r) \<and> y \<in> (CC r) \<and> (x \<noteq> y)) \<longrightarrow> (r x y \<or> r y x))"    
  
abbreviation K:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" ("K_")
where "K r \<equiv> ((connected r) \<and> (transitive r) \<and> (irreflexive r))"

section "Proof of Lemma T"  
  
text "Sledgehammer can prove the Lemma directly"  
lemma Tauto: "((\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))   \<and>  (K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))" by (metis (no_types, lifting) CollectI)

text "Using the steps from Salamucha is actually worse performancewise (and needs smt)"

lemma T: "((\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))   \<and>  (K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))"
proof -
    have  one: "(\<forall>x. ((f x ) \<longrightarrow> (\<exists>t. (R t x)))) \<longrightarrow> (\<forall>x. ((\<forall>t. (\<not> R t x)) \<longrightarrow> (\<not> f x)))"  by blast 
    have twoa: "(K R) \<longrightarrow> (\<forall>y u. (R y u \<longrightarrow> \<not> R u y))" by blast
    have twob: "(K R) \<longrightarrow> (\<forall>y u. ((u \<in> (CC R) \<and> u \<noteq> y \<and> R y u) \<longrightarrow> (\<not> R u y) ))" by meson
 
(*Note that in the second version of Salamuchas notation (the boxed one) there is a consistent typo.
The y in the Consequens of almost all formulas should be a v*)    
    have threea: "((K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))  \<longrightarrow> 
(\<exists>v. (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u)))) " by meson  
    have threeb: "((K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ( (u \<in> (CC R) \<and> u \<noteq> y ) \<longrightarrow> (R y u))))))
\<longrightarrow> (\<exists>v. (\<forall>u. ( (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (\<not> R u v) )))" by (metis (mono_tags, lifting))  
    (*Note that neither threea nor twob is used*)    
    have threec: "((K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ( (u \<in> (CC R) \<and> u \<noteq> y ) \<longrightarrow> (R y u))))))
\<longrightarrow> (\<exists>v. (\<forall>u. ( (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (\<not> R u v \<and> R v u))))" by meson
    have four:  "((K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ( (u \<in> (CC R) \<and> u \<noteq> y ) \<longrightarrow> (R y u))))))
\<longrightarrow> (\<exists>v. ((\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (\<not> R u v))) \<and> (\<forall>u. ( (u \<in> (CC R) \<and> (u \<noteq> v)) \<longrightarrow> (R v u))) ))" by meson
    have five: "\<forall>u v. ((\<not> (u \<in> (CC R))) \<longrightarrow> (\<not> R u v))" by simp
    have six: "(K R) \<longrightarrow> (\<forall>u v. (u = v \<longrightarrow> (\<not> R u v)))" by simp   
    have seven: "((K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ( (u \<in> (CC R) \<and> u \<noteq> y ) \<longrightarrow> (R y u))))))
\<longrightarrow> (\<exists>v. ((\<forall>u. ((\<not> R u v) )) \<and> (\<forall>u.((u \<in> (CC R) \<and> (u \<noteq> v)) \<longrightarrow> (R v u)))))" using five six four 
      by (smt ext) (*Warning: this is an smt proof other proof methods fail here [but if need be the proof can be made explicit*)
    have eigth:  "((\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))) \<and> (K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ( (u \<in> (CC R) \<and> u \<noteq> y ) \<longrightarrow> (R y u))))))
\<longrightarrow> (\<exists>v. (((\<not> f v) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))))" using seven one by meson
    then show ?thesis by blast
qed

text "The first two conjuncts of the antecedents of T imply the stronger Thesis T1"

lemma TtoT1:
assumes firsttwoT: "(K R) \<and> (\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))"  
shows "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using firsttwoT by blast (*very slow*)
    
text "Are the conjuncts of the antecedent of Thesis T all necessary?"
  
lemma T12: "((\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))   \<and>  (K R) )
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))"
  nitpick[verbose] (*Nitpick does NOT find a counterexample; perhaps someone with more computing power could run this again*)
(*Salamucha gives the following counterexample (p.115f): Let R be the greater-than relation on
the positive natural numbers. Let f x mean that x is a positive number (hold trivially).
Since > is an ordering relation and there always is a bigger number the antecedents hold.
There is however no positive number that is not positive therefore the conditional is false.*)
oops
lemma T13: "((\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))   \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))"
  nitpick[verbose] (*nitpick finds a counterexample*)
oops    
lemma T23: "( (K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))"
    nitpick[verbose] (*nitpick finds a counterexample*)   
oops

  
section "Proof of Thesis T1"  

text "fast can prove T1 in ~ 1s"  
lemma T1auto:
assumes onea: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and oneb: "\<forall>x. ((\<exists>a b. ((a M x \<and> b M x) \<and> ((\<not> f a \<and> f b) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))) )) \<longrightarrow> (\<not> R x x))"
and onec: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. (R t x)))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using onea oneb onec by fast
(*N.B.: Salamucha implies that this proof hold for other definitions of identities as well*)
    
    
    
text "Now with Salamuchas more expicit proof"    
lemma T1:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 13: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. (R t x)))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))"    
proof -
   (*have True nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick confirms consistency*) *)
  have onea: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))" using 11 by blast
  have oneb: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x) \<and> ((\<not> f a) \<and> f b) \<or> (f a \<or> (\<not> f b))))" using onea by auto
  have onec: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x) \<and> ((\<not> f a) \<and> f b) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))" using oneb by blast           
  
      (*Contrary to what Salamucha thinks the next step needs both 11 and 12 not just 12; see below.*)
  have two: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<not> (\<exists>a b. (a M x \<and> b M x) \<and> ((\<not> f a) \<and> f b) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))   )" using 12 onea by blast 
  have threea: "\<forall>x. ((\<not> f x) \<or> (\<not> R x x))" using two onec by blast
  have threeb: "\<forall>x. (f x \<longrightarrow> (\<exists>t. ( (R t x) \<and> (\<not> R x x))))" using 13 threea by auto
  have threec: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x \<and> t \<noteq> x)))" using threeb by fast
thus ?thesis by simp
qed      

  
text "12 does not imply two"
         
lemma "(\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))) \<longrightarrow> (\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<not> (\<exists>a b. (a M x \<and> b M x) \<and> ((\<not> f a) \<and> f b) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))   ))"
nitpick[verbose]
  oops
    
text "Are all assumptions necessary?"    
lemma T1wo1:
assumes 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 13: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. (R t x)))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" 
nitpick[verbose] (*Nitpick doesn\<acute>t find a counterexample *)
(*For a counterexample consider:
x R y := x = y
f x := True
x M y := False
12 then simlifies to: "\<forall>x. (False \<longrightarrow> (\<not> R x x))" which holds
13 is trivally true (for t = x)
The thesis doesn\<acute>t hold.
*)  
oops  

lemma T1wo2:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 13: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. (R t x)))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" 
nitpick[verbose] (*Nitpick doesn\<acute>t find a counterexample*)
(*For an easy counterexample consider
x R y := x = y
x M y := True
f x := \<exists>t. (R t x)
then both 11 and 13 hold but clearly the thesis is wrong*)
oops
    
lemma T1wo3:    
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))"     
nitpick[verbose] (*Nitpick doesn\<acute>t find a counterexample*)   
(*
For a counterexample consider:
x R y := False
x M y := True
f x : = True
11 holds trivially and the thesis is false
for 12 we have: "\<forall>x. (\<exists>a b. ((True \<and> (False \<or> True)) \<longrightarrow> True)"
ergo: "\<forall>x. \<exists>a b. (True)" which is a theorem.
*)
oops
  
section "Irreflexivity of R"

text "first automated"
  
lemma irreflexivityRauto:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows  "irreflexive R" using 11 12 14 by presburger  

text "then using the steps in Salamuchas book"
  
lemma irreflexivityR:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows  "irreflexive R"    
proof -
  (*have True nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick runs out of time*) *)

  (*Steps until threea are the same as in the proof of T1*)
  have onea: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))" using 11 by blast
  have oneb: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x) \<and> ((\<not> f a) \<and> f b) \<or> (f a \<or> (\<not> f b))))" using onea by auto
  have onec: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x) \<and> ((\<not> f a) \<and> f b) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))" using oneb by blast           
  have two: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<not> (\<exists>a b. (a M x \<and> b M x) \<and> ((\<not> f a) \<and> f b) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))   )" using 12 onea by blast 
  have threea: "\<forall>x. ((\<not> f x) \<or> (\<not> R x x))" using two onec by blast
  have foura: "\<forall>x y. ((R x y) \<longrightarrow> (\<not> R y y))" using 14 threea by fastforce
  have fourb: "\<forall>x y. ((R x y) \<longrightarrow> ((R x y) \<and> (\<not> R y y)))" using foura by simp
  have fourc: "\<forall>x y. ((R x y) \<longrightarrow> (x \<noteq> y))" using fourb by fast   
thus ?thesis by auto
qed      

text "Are the assumption all necessary?"
lemma irreflexivityRwo1:
assumes 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows  "irreflexive R" 
nitpick[verbose] (*Nitpick runs out of time*)
(*For a counterexample consider: x R y := x = y; x M y := False; f x := False*)    
oops    

lemma irreflexivityRwo2:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows  "irreflexive R" 
nitpick[verbose] (*Nitpick runs out of time*)
(*For a counterexample consider: x R y := x = y; f x := False; x M y := False*)
oops  

lemma irreflexivityRwo4:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
shows  "irreflexive R"   
nitpick[verbose] (*Nitpick finds a counterexample*)
oops


text "Show that the weaker assumption doesn\<acute>t work to prove irreflexivity"  
lemma weaker12:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and w12: "\<forall>x.((\<exists>a b. ( (a M x \<and> b M x) \<and> \<not> (f a \<longleftrightarrow> f b)  )) \<longrightarrow> (\<not> R x x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows  "irreflexive R"  
nitpick[verbose] (*Nitpick finds a counterexample*) 
oops

  
section "The third proof"
  
(*If we don\<acute>t give Isabelle a type for S the proof won\<acute>t work. I don\<acute>t know why that is.
Perhaps someone who knows more about the inner workings of Isabelle\<acute>s typed logic can help me out here*)
text "first automated"

lemma thirdproofauto:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 24: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
shows "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using 21 22 23 24 by blast
  
lemma thirdproof:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 24: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
shows "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" 
proof -
  (*have True nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick confirms consistency*) *)
  have one: "\<forall>x y. ((x A\<^sub> R y) \<longrightarrow> \<not>(x P\<^sub> R y))" using 21 by simp
  have two: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> ((x P\<^sub> R y) \<and> (y A\<^sub> R x)))" using 22 23 by simp   
  have threea: "\<forall>x.((f x \<and> (R x x)) \<longrightarrow> ((x P\<^sub> R x) \<and> (x A\<^sub> R x)))" using two by simp
  have threeb: "\<forall>x.((f x \<and> (R x x)) \<longrightarrow> \<not>((x A\<^sub> R x) \<longrightarrow> \<not>(x P\<^sub> R x)))" using threea by simp
  have four: "\<forall>x. ((x A\<^sub> R x) \<longrightarrow> \<not>(x P\<^sub> R x))" using one by simp
  have five: "\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> ((x A\<^sub> R x) \<longrightarrow> \<not> (x P\<^sub> R x)))" using four by simp
  have six: "\<forall>x. (f x \<longrightarrow> \<not> (R x x))" using five threeb by simp
  have seven: "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> \<not>(R x x))))" using 24 six by simp
  have eight: "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using seven by fastforce
thus ?thesis by simp
qed      

  
text "Are all assumptions necessary?"

lemma thirdproofwo1:
assumes 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 24: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
shows "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))"
nitpick[verbose] (*Nitpick finds a counterexample*)
  oops
    
lemma thirdproofwo2:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 24: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
shows "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))"
nitpick[verbose] (*Nitpick finds a counterexample*)
oops

lemma thirdproofwo3:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 24: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
shows "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))"  
nitpick[verbose] (*Nitpick finds a counterexample*)
oops

lemma thirdproofwo4:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
shows "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))"  
nitpick[verbose] (*Nitpick finds a counterexample*) 
oops    


text "Next we show that also assumptions 21 22 23 and 14 imply irreflexivity"  

lemma IrreflexivityRv2:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows "irreflexive R"
(*proof -  nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick confirms consistency*) *) 
using 21 22 23 14 by meson



text "Are the assumptions all necessary?"
  
lemma IrreflexivityRv2wo1:
assumes 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows "irreflexive R"
nitpick[verbose] (*Nitpick finds a counterexample*) 
oops
    
lemma IrreflexivityRv2wo2:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows "irreflexive R"
nitpick[verbose] (*Nitpick finds a counterexample*) 
oops  
 
lemma IrreflexivityRv2wo3:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows "irreflexive R"  
nitpick[verbose] (*Nitpick finds a counterexample*) 
oops

lemma IrreflexivityRv2wo4:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
shows "irreflexive R"  
nitpick[verbose] (*Nitpick finds a counterexample*) 
oops  
  
  
section "Arguments for there being a first element"


(*N.B. my local sledgehammer (and try0 etc.) can t prove the following theorem; the only remote prover
that finds a proof is vampire but proof reconstruction fails even here.
I would be interested if sledgehammer finds a proof on a faster machine.
Useful theorems to add are mem_Collect_eq and perhaps Tauto*)   
  
lemma TpThenNotC3:
assumes Tp: "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"
and c1: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
and c2: "K R"
shows "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>u. ((u \<in> (CC R) \<and> u \<noteq> x) \<and> (\<not> R x u))))" 
proof -
(*  nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick doesn\<acute>t find a model.
That is however not really of importance since this is (sort of) supposed to be a reductio*) *)
  have one: "\<forall>x y. ((R y x) \<longrightarrow> (f y \<and> f x))" using Tp by fastforce
  have two: "\<forall>x y. ((R x y \<or> R y x) \<longrightarrow> (f x \<and> f y))" using one Tp by blast
  have threea: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>t. (R t x \<or> R x t)))" by auto
  have threeb: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>t. (f x \<and>  f t)))" using threea two by blast
  have threec: "\<forall>x. (x \<in> (CC R) \<longrightarrow> f x)" using threeb by blast   
  have threed: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>u. (R u x)))" using threec c1 by simp
  have threee: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>u. ((u \<in> (CC R) \<and> u \<noteq> x) \<and> (\<not> R x u))))" 
  proof - (*In this house we do what the provers do, son!*)
    { fix aa :: a
    obtain aaa :: "a \<Rightarrow> a" where
      ff1: "\<forall>a. a \<notin> CC R \<or> R (aaa a) a"
      by (metis (lifting) threed) (* 0.0 ms *)
    { assume "\<not> R aa aa \<and> aa \<in> CC R"
      then have "aa \<noteq> aaa aa"
        using ff1 by (metis (lifting)) (* 31 ms *)
      moreover
      { assume "aa \<noteq> aaa aa \<and> aa \<in> CC R"
        then have "(\<exists>a. R (aaa aa) a \<or> R a (aaa aa)) \<and> aa \<noteq> aaa aa"
          using ff1 by meson (* 31 ms *)
        then have "aaa aa \<in> CC R \<and> aa \<noteq> aaa aa"
          using mem_Collect_eq by blast (* 0.0 ms *)
        then have "R aa (aaa aa) \<or> aa \<notin> CC R \<or> (\<exists>a. a \<in> CC R \<and> aa \<noteq> a \<and> \<not> R aa a)"
          by (metis (lifting)) (* 0.0 ms *)
        moreover
        { assume "R aa (aaa aa)"
          then have "aa \<notin> CC R \<or> (\<exists>a. a \<in> CC R \<and> aa \<noteq> a \<and> \<not> R aa a)"
            using ff1 by (meson c2) (* 0.0 ms *) }
        ultimately have "aa \<notin> CC R \<or> (\<exists>a. a \<in> CC R \<and> aa \<noteq> a \<and> \<not> R aa a)"
          by blast (* 0.0 ms *) }
      ultimately have "aa \<notin> CC R \<or> (\<exists>a. a \<in> CC R \<and> aa \<noteq> a \<and> \<not> R aa a)"
        by blast (* 0.0 ms *) }
    then have "aa \<notin> CC R \<or> (\<exists>a. a \<in> CC R \<and> aa \<noteq> a \<and> \<not> R aa a)"
      by (meson c2) (* 0.0 ms *) }
  then show ?thesis
    by (metis (lifting)) (* 15 ms *) qed
thus ?thesis by blast
qed
  
text "whether the assumptions are all necessary is irrelevant here (since it\<acute>s supposed to be a reductio)."

(*To Be Continued (p. 126*)
  
(*
 
and 31: "\<forall>x. (f x \<longrightarrow> C x)"
and 32: "\<forall>x. ((C x \<and> f x) \<longrightarrow> (\<exists>t\<^sub>1. (t\<^sub>1 F x)))"
and 33: "\<forall>x t\<^sub>2. (C x \<longrightarrow> ((t\<^sub>2 F x) \<longrightarrow> (H t\<^sub>2)))"
and 34: "\<forall>x y t\<^sub>1 t\<^sub>2. (((R x y) \<and> ((t\<^sub>1 F x) \<and> (t\<^sub>2 F y))) \<longrightarrow> (t\<^sub>1 = t\<^sub>2))"
*)  




end