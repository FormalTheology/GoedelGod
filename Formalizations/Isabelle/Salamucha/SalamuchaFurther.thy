theory SalamuchaFurther

imports Main

begin
text {*
This file is for further investigation and automation of Salamucha\<acute>s Ex Motu proof.
For a reconstruction of the steps in Salamucha\<acute>s paper see the Salamucha.thy theory file.
*}

section "Types and Definitions"

text "We will use a single type a for all objects"
typedecl a 

text "We will write (x R y) or (R x y) for \<acute>x moves y\<acute>"  
consts R:: "a \<Rightarrow> a \<Rightarrow> bool" (*(infixr "R"52)*)

text "We will write (f x) for x is in motion\<acute>"  
consts f :: "a \<Rightarrow> bool"
  
text "We will write (p M Q) for \<acute>p is a proper part of Q\<acute>"  
consts partof :: "a \<Rightarrow> a \<Rightarrow> bool" (infixr "M"52)
 
text "we will write (x A_S Y) for \<acute>x is in aspect S in actu to y\<acute>"  
consts aspactu :: "a \<Rightarrow> 'a \<Rightarrow> a \<Rightarrow> bool" ("_A\<^sub>_ _") 

text "we will write (x P_S Y) for \<acute>x is in aspect S in potentia to y\<acute>"  
consts asppot :: "a \<Rightarrow> 'a \<Rightarrow> a \<Rightarrow> bool" ("_ P\<^sub>_ _") 

text "Let (C x) mean \<acute>x is a body\<acute>"
consts body:: "a \<Rightarrow> bool" ("C")
  
text "Next let (t F x) stand for \<acute>t is the duration of movement of x\<acute>"  
consts duration :: "'a \<Rightarrow> a \<Rightarrow> bool" ("_ F _") (*we could use a "time type". But I don\<acute>t see much use*)

text "Similarly, we will write (H t) for \<acute>t is the finite period of time\<acute>[sic]."  
consts finitetime :: "'a \<Rightarrow> bool" ("H") 
  
text "We abbreviate the set of things that move something or are moved by something as follows"  
abbreviation CC:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" 
  where "CC r \<equiv> {a. \<exists>t. ((r a t) \<or> (r t a))}"
(*Salamucha has C\<acute>R *)
  
abbreviation irreflexive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "irreflexive r \<equiv> (\<forall>x. \<not> (r x x))"   

abbreviation transitive :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "transitive r \<equiv> (\<forall>x y z. ((r x y) \<and> (r y z) \<longrightarrow> ( r x z)))"   

abbreviation connected :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  where "connected r \<equiv> \<forall>x y. ((x \<in> (CC r) \<and> y \<in> (CC r) \<and> (x \<noteq> y)) \<longrightarrow> (r x y \<or> r y x))"    
  
text "We call a relation an Ordering Relation if it is connected, transitive and irreflexive; or K for short."
abbreviation K:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" ("K_")
where "K r \<equiv> ((connected r) \<and> (transitive r) \<and> (irreflexive r))"

  
section "Proof of Lemma T"  
  
lemma T: "((\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))   \<and>  (K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))" by (metis (no_types, lifting) CollectI)

text "The first two conjuncts of the antecedents of T imply the stronger thesis T1"

lemma TtoT1:
assumes firsttwoT: "(K R) \<and> (\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))"  
shows "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using firsttwoT by blast (*very slow*)
    
text "Are the conjuncts of the antecedent of thesis T all necessary?"
  
lemma Two3: "((\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))   \<and>  (K R) )
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))"
  nitpick[verbose] 
  oops
(*"Nitpick does not find a counterexample; perhaps someone with more computing power could run this again
Salamucha gives the following counterexample (p.115f): Let R be the greater-than relation on
the positive natural numbers. Let f x mean that x is a positive number (holds trivially).
Since > is an ordering relation and there always is a bigger number, the antecedents hold.
There is however no positive number that is not positive therefore the conditional is false."*)    
        
lemma Two2: "((\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x))))   \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))"
  nitpick[verbose] (*Nitpick finds a counterexample*)
  oops
    
lemma Two1: "( (K R) \<and> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))
\<longrightarrow>  (\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))"
nitpick[verbose]  (*Nitpick finds a counterexample*)
oops


section "Proof of thesis T1"  

lemma T1:
assumes onea: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and oneb: "\<forall>x. ((\<exists>a b. ((a M x \<and> b M x) \<and> ((\<not> f a \<and> f b) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))) )) \<longrightarrow> (\<not> R x x))"
and onec: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. (R t x)))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using onea oneb onec by fast
(*N.B.: Salamucha implies that this proof holds for other definitions of identities as well"*)
    
text "In the original proof Salamucha claims that 12 implies step two. 
This is not true."
         
lemma "(\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))) \<longrightarrow> (\<forall>x. ((f x \<and> (R x x)) \<longrightarrow> (\<not> (\<exists>a b. (a M x \<and> b M x) \<and> ((\<not> f a) \<and> f b) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))   ))"
nitpick[verbose] (*Nitpick finds a counterexample*)
  oops
    
text "Are all assumptions necessary?"    
lemma T1wo1:
assumes 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 13: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. (R t x)))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" 
nitpick[verbose] (*Nitpick finds a counterexample*)    
  oops
    
lemma T1wo2:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 13: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. (R t x)))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" 
nitpick[verbose] 
oops (*Nitpick finds a counterexample*)
  
lemma T1wo3:    
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
shows  "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))"     
nitpick[verbose] (*Nitpick finds a counterexample*)
oops

  
section "Irreflexivity of R"

lemma irreflexivityR:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows  "irreflexive R" using 11 12 14 by presburger  
    
text "Are all assumptions necessary?"
lemma irreflexivityRwo1:
assumes 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows  "irreflexive R" 
nitpick[verbose] (*Nitpick finds a counterexample*)    
  oops    

lemma irreflexivityRwo2:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows  "irreflexive R" 
nitpick[verbose] (*Nitpick finds a counterexample*) 
oops  

lemma irreflexivityRwo4:
assumes 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
shows  "irreflexive R"   
nitpick[verbose] (*Nitpick finds a counterexample*)
oops

text "Show that the weaker assumption does not work to prove irreflexivity"  
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

lemma thirdproof:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 24: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
shows "\<forall>x. (f x \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using 21 22 23 24 by blast
  
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

text "Next we show that assumptions 21 22 23 and 14 also imply irreflexivity"  

lemma IrreflexivityRv2:
assumes 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
shows "irreflexive R"
(*proof -  nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick confirms consistency*) *) 
using 21 22 23 14 by meson

text "Are all assumptions  necessary?"
  
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
  
section "Arguments for there being a first Element"

(*N.B. my local sledgehammer (and try0 etc.) can not prove the following theorem; the only remote prover
that finds a proof is vampire but proof reconstruction fails even here.
I would be interested if sledgehammer finds a proof on a faster machine.
Useful theorems to add are mem_Collect_eq and perhaps T*)
  
lemma TpThenNotC3:
assumes Tp: "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"
and c1: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
and c2: "K R"
shows "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>u. ((u \<in> (CC R) \<and> u \<noteq> x) \<and> (\<not> R x u))))" 
proof -
(*  nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick doesn\<acute>t find a model.
However, this is not really of importance since the proof is (sort of) supposed to be a reductio*)*)
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

text "Arguments for Tp (for a reductio)"

lemma Tp:
assumes c2: "K R"  
and NotC3: "\<not> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u)))))"
and 35: "\<forall>x. ((\<exists>t. (t R x)) \<longrightarrow> f x)"
shows  "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"  using c2 NotC3 35 by meson

text "Are all assumptions necessary? (kind of an academic question, since this is supposed to be a reductio)"
text "No!"
  
lemma Tpwo1:
assumes NotC3: "\<not> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u)))))"
and 35: "\<forall>x. ((\<exists>t. (t R x)) \<longrightarrow> f x)"
shows  "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"  using NotC3 35 by meson

lemma Tpo2:
assumes c2: "K R"  
and 35: "\<forall>x. ((\<exists>t. (t R x)) \<longrightarrow> f x)"
shows  "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"    
nitpick[verbose]  
oops
(*Nitpick doesn\<acute>t find a counterexample*)
(*For a counterexample consider:
Let R be a relation on the natural numbers (n \<ge> 0) where:
x R y := x = 0 \<and> y = 1
R is transitive, irreflexive and connected hence c2 holds.
Let f x := \<exists>t. (t < x)
then, if t R x holds then t = 0 and x = 1 and there is a smaller number than 1, namely 0.
Hence 35 holds.
However for x = 0 and y = 1, x R y holds but it is not true that f 0, since by definition
there is no smaller natural number*)
  
lemma Tpwo3:
assumes c2: "K R"  
and NotC3: "\<not> (\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u)))))"
shows  "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"       
nitpick[verbose] 
oops      
(*Nitpick doesn\<acute>t find a counterexample*)
(*For a (trivial) counterexample consider:
let R be the less-than relation on \<int>. It is obviously an Ordering Relation.
There is also no smallest element. Therefore c2 and NotC3 hold.
let f x := False.
Then the conclusion is wrong for all x y.
*)

(*For the following lemma sledgehammer proof reconstruction fails, but the results strongly suggest
that the set of assumptions are inconsistent.
This is however not a problem since the intention of this lemma is to show 
that Tp should be rejected*)  
  
lemma Unwantedconsequences: 
assumes 31: "\<forall>x. (f x \<longrightarrow> C x)"
and 32: "\<forall>x. ((C x \<and> f x) \<longrightarrow> (\<exists>(t\<^sub>1::a). (t\<^sub>1 F x)))"
and 33: "\<forall>x (t\<^sub>2::a). (C x \<longrightarrow> ((t\<^sub>2 F x) \<longrightarrow> (H t\<^sub>2)))"
and 34: "\<forall>x y (t\<^sub>1::a) (t\<^sub>2::a). (((R x y) \<and> ((t\<^sub>1 F x) \<and> (t\<^sub>2 F y))) \<longrightarrow> (t\<^sub>1 = t\<^sub>2))"
and c2: "K R"  
and Tp: "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"
shows "\<forall>x y (t\<^sub>1::a) (t\<^sub>2::a).((x \<in> (CC R) \<and> y \<in> (CC R) \<and> (x \<noteq> y) \<and> (t\<^sub>1 F x) \<and> (t\<^sub>2 F y))   \<longrightarrow> t\<^sub>1 = t\<^sub>2)"
proof -
  have one: "\<forall>x y. ((R x y \<or> R y x) \<longrightarrow> (f x \<and> f y))" using Tp by auto  
  have twoa: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>z. (R z x \<or> R x z)))" by auto
  have twob: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>z. (f z \<and> f x)))" using twoa one by meson
  have twoc: "\<forall>x. (x \<in> (CC R) \<longrightarrow> f x)" using twob by simp
  have three: "\<forall>x. (x \<in> (CC R) \<longrightarrow> C x)" using twoc 31 by blast
  have four: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (C x \<and> f x))" using three twoc by simp    
  have five: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>(t\<^sub>1::a). (t\<^sub>1 F x)))" using four 32 by blast
  have six: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<forall>(t\<^sub>2::a). ((t\<^sub>2 F x) \<longrightarrow> (H t\<^sub>2))))" using three 33 by blast   
  (*step seven has a typo in the \<acute>boxed notation\<acute>*)
  have seven: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>(t\<^sub>1::a). ((t\<^sub>1 F x) \<and> (H t\<^sub>1))))" using five six by blast
  have eight: "\<forall>x y (t\<^sub>1::a) (t\<^sub>2::a). (((R x y \<or> R y x) \<and> ((t\<^sub>1 F x) \<and> (t\<^sub>2 F y))) \<longrightarrow> t\<^sub>1 = t\<^sub>2)" using 34 by blast
  have nine: "\<forall>x y (t\<^sub>1::a) (t\<^sub>2::a).((x \<in> (CC R) \<and> y \<in> (CC R) \<and> (x \<noteq> y) \<and> (t\<^sub>1 F x) \<and> (t\<^sub>2 F y))   \<longrightarrow> t\<^sub>1 = t\<^sub>2)" using eight c2 by meson (*slow*) 
  thus ?thesis by blast
qed      
(*N.B. Salamucha mentions that for some definitions of identity (e.g. a Leibnizian)
the x \<noteq> y can be omitted in none. He argues that this is however not very helpful
and leads to more problems than the apparent simplification solves. I tend to agree.*)  
  
section "The Consequens of Thesis T"
  
text "Ex Motu implies monotheism"  

lemma Monotheism:
assumes god: "(\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))))"  
and c2: "K R"
and c3: "(\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u)))))"
shows "((\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u))) \<and> (\<not> (f w) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> w) \<longrightarrow> (R w u))))
\<longrightarrow> v = w" using c2 c3 god  by (metis (full_types, lifting) mem_Collect_eq)


section "The entire proof(s) (as specified on p.131ff)"    
  
text {*
Salamucha offers several different ways to combine sets of assumptions to get the conclusion. Only those that have been formalized in the paper (and are not just natural language assumptions) are proven here.
Even those two possible combinations however rely on an additional assumption "A" [that Salamucha claims follows from two other assumptions that are only stated in natural language].

In the (apparently somewhat sloppy) translation A is stated as:
"An infinite and ordered set of moving bodies and bodies that move is not in motion for the limited period of time [sic]."

The best fit for this seems to be the formula "A" below. 
It makes the argument valid, uses the same concepts and fits neatly in the dialectic the previous reductio arguments provide.
*}  

lemma AC:
assumes one: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
and two: "\<forall>x y z. (((R x y) \<and>  (R y z)) \<longrightarrow> (R x z))"    
and three: "\<forall>x y. ((x \<in> (CC R) \<and> y \<in> (CC R) \<and> (x \<noteq> y)) \<longrightarrow> ((R x y) \<or> (R y x)))"
(*A*)
and 11: "\<forall>x. ((f x) \<longrightarrow> (\<exists>a b. (a M x \<and> b M x)))"
and 12: "\<forall>x. ((\<exists>a b. (((a M x) \<and> (b M x)) \<and> (((\<not> f a) \<and> (f b)) \<or> ((\<not> f a) \<longrightarrow> (\<not> f b))))) \<longrightarrow> (\<not> R x x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)" 
(*C*)
and 31: "\<forall>x. (f x \<longrightarrow> C x)"
and 32: "\<forall>x. ((C x \<and> f x) \<longrightarrow> (\<exists>(t\<^sub>1::a). (t\<^sub>1 F x)))"
and 33: "\<forall>x (t\<^sub>2::a). (C x \<longrightarrow> ((t\<^sub>2 F x) \<longrightarrow> (H t\<^sub>2)))"
and 34: "\<forall>x y (t\<^sub>1::a) (t\<^sub>2::a). (((R x y) \<and> ((t\<^sub>1 F x) \<and> (t\<^sub>2 F y))) \<longrightarrow> (t\<^sub>1 = t\<^sub>2))"
and 35: "\<forall>x. ((\<exists>t. (t R x)) \<longrightarrow> f x)"
(*A*)
and A: "\<not> (\<forall>x. (x \<in> {y. (y \<in> (CC R) \<and> (C y))} \<longrightarrow> (\<exists>t\<^sub>1::a. ((t\<^sub>1 F x) \<and> (H t\<^sub>1)))))" (*It is not the case that all moving bodies
move only a (the?) limited period of time (negation of "seven" from unwanted consequences*)
shows "\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u)))" 
proof -
(*nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick runs out of time!*) *) 
(*This should really be investigated further*)
  from 11 12 14 have "irreflexive R" using irreflexivityR by blast
  hence c2: "K R" using one two three by blast
  have T1: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using 11 12 14 T1 one by blast
  hence c1: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))" by blast
  {assume Tp: "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"
   have seven: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>(t\<^sub>1::a). ((t\<^sub>1 F x) \<and> (H t\<^sub>1))))" using Tp 31 32 33 by blast
   hence False using A by blast}
  hence NOTTp: "\<not> (\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y)))" by blast
  {assume NOTC3:  "\<not> ((\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))"    
    have False using Tp 35 NOTTp c2 NOTC3 by blast}
  hence c3: "((\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))" by blast   
show ?thesis using  c1 c2 c3 T by blast
qed
  
lemma BC:
assumes one: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))"
and two: "\<forall>x y z. (((R x y) \<and>  (R y z)) \<longrightarrow> (R x z))"    
and three: "\<forall>x y. ((x \<in> (CC R) \<and> y \<in> (CC R) \<and> (x \<noteq> y)) \<longrightarrow> ((R x y) \<or> (R y x)))"
(*B*)
and 21: "\<forall>x y (S::a \<Rightarrow> a \<Rightarrow> bool). ((x A\<^sub> S y) \<longrightarrow> \<not>(x P\<^sub> S y))"
and 22: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (x P\<^sub> R y))"  
and 23: "\<forall>x y. ((f x \<and> (R y x)) \<longrightarrow> (y A\<^sub> R x))"
and 14: "\<forall>x y.(x R y \<longrightarrow> f y)"
(*C*)
and 31: "\<forall>x. (f x \<longrightarrow> C x)"
and 32: "\<forall>x. ((C x \<and> f x) \<longrightarrow> (\<exists>(t\<^sub>1::a). (t\<^sub>1 F x)))"
and 33: "\<forall>x (t\<^sub>2::a). (C x \<longrightarrow> ((t\<^sub>2 F x) \<longrightarrow> (H t\<^sub>2)))"
and 34: "\<forall>x y (t\<^sub>1::a) (t\<^sub>2::a). (((R x y) \<and> ((t\<^sub>1 F x) \<and> (t\<^sub>2 F y))) \<longrightarrow> (t\<^sub>1 = t\<^sub>2))"
and 35: "\<forall>x. ((\<exists>t. (t R x)) \<longrightarrow> f x)"
(*A*)
and A: "\<not> (\<forall>x. (x \<in> {y. (y \<in> (CC R) \<and> (C y))} \<longrightarrow> (\<exists>t\<^sub>1::a. ((t\<^sub>1 F x) \<and> (H t\<^sub>1)))))"
shows "\<exists>v. (\<not> (f v) \<and> (\<forall>u. (u \<in> (CC R) \<and> u \<noteq> v) \<longrightarrow> (R v u)))" 
(*nitpick [satisfy, user_axioms, expect = genuine] (*Nitpick runs out of time again*)*)
proof -
  from 21 22 23 14 have "irreflexive R" using  IrreflexivityRv2 by blast
  hence c2: "K R" using one two three by blast
  have T1: "\<forall>x. ((f x) \<longrightarrow> (\<exists>t. ((R t x) \<and> t \<noteq> x)))" using 21 22 23 one thirdproof by blast
  hence c1: "\<forall>x. (f x \<longrightarrow> (\<exists>t. (R t x)))" by blast
  {assume Tp: "\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y))"
   have seven: "\<forall>x. (x \<in> (CC R) \<longrightarrow> (\<exists>(t\<^sub>1::a). ((t\<^sub>1 F x) \<and> (H t\<^sub>1))))" using Tp 31 32 33 by blast
   hence False using A by blast}
  hence NOTTp: "\<not> (\<forall>x y. ((R x y) \<longrightarrow> (f x \<and> f y)))" by blast
  {assume NOTC3:  "\<not> ((\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))"    
    have False using Tp 35 NOTTp c2 NOTC3 by blast}
  hence c3: "((\<exists>y. (y \<in> (CC R) \<and> (\<forall>u. ((u \<in> (CC R) \<and> u \<noteq> y) \<longrightarrow> (R y u))))))" by blast   
  show ?thesis using  c1 c2 c3 T by blast
qed      
end