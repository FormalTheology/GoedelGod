theory Jarret
  
  imports QMLBiMod
  
begin
(*This is an automation of a formalization of Spinoza\<acute>s Ethics I by Jarret.
For the corresponding paper \<acute>The logical structure of Spinoza's Ethics, Part I\<acute>
see: https://link.springer.com/article/10.1007%2FBF00869440*)
  
section "(Some) Rules of inference" (*For the semantic embedding see the imported QML file*)
lemma R1: "\<lfloor>\<^bold>L P\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>N P\<rfloor>" using NS5U  by simp  
lemma R2: "\<lfloor>\<^bold>N P\<rfloor> \<Longrightarrow> \<lfloor>P\<rfloor>" using LM by auto
lemma R3: "\<lfloor>\<^bold>L (P \<^bold>\<rightarrow> Q)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>L P \<^bold>\<rightarrow> \<^bold>L Q\<rfloor>" by auto
lemma R4: "\<lfloor>\<^bold>M P\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>L \<^bold>M P\<rfloor>" using NS5U  by simp  
lemma R5: "\<lfloor>P\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>L P\<rfloor>" by simp  
lemma R6: "\<lfloor>\<^bold>N (P \<^bold>\<rightarrow> Q)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>N P \<^bold>\<rightarrow> \<^bold>N Q\<rfloor>" by auto

lemma DR1: "\<lfloor>\<^bold>L P\<rfloor> \<Longrightarrow> \<lfloor>P\<rfloor>" by (simp add: NS5U)

section "Constants and Terms"

text "x is conceived through y"   
consts  Cxy::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("C") 

text "x limits y"
consts  Lxy::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("L")
  
text "x is a cause of y"  
consts  Kxy::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("K")

text "x is common to y and z"  
consts  Cxyz::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("C")
  
text "x is an object of y"  
consts  Oxy::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("O")
  
text "The next constant is needed but not introduced in part III. Best guess is:
x corresponds to y"  
consts  Hxy::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("H") (*not introduced in III;
N.B.: The only axiom that needs H (A6) is superfluous.*)
  
text "x is true"
consts  T::"\<mu> \<Rightarrow> \<sigma>" ("T")

text "x is an idea"  
consts  K::"\<mu> \<Rightarrow> \<sigma>" ("K") 
  
text "x is divisible into y and z"  
consts  Dxyz::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<mu>  \<Rightarrow> \<sigma>" ("D")
  
text "x is an intellect"  
consts  U::"\<mu> \<Rightarrow> \<sigma>" 
  
text "x is a will"  
consts  W::"\<mu> \<Rightarrow> \<sigma>" 
  
text "x is (an instance of) love"  
consts  J::"\<mu> \<Rightarrow> \<sigma>"
  
text "x is (an instance of) desire"
consts  D::"\<mu> \<Rightarrow> \<sigma>" ("D")
  
text "x has more reality than y"  
consts  Rxy::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("R")
  
text "x has more attributes than y"  
consts  Vxy::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("V")

text "x is the power of y"  
consts  Pxy::"\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("P")
  
section "Definitions" (*Order changed to avoid reference to yet undefined constants*)

abbreviation D9:: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("I _ _") (*See p. 44*)
  where "(I (x::\<mu>) (y::\<mu>)) \<equiv> ( (x \<^bold>\<noteq> y) \<^bold>\<rightarrow> (\<^bold>L ((\<^bold>\<exists>v. (v \<^bold>= x)) \<^bold>\<rightarrow> (\<^bold>\<exists>v. (v \<^bold>= y)))))
\<^bold>\<and> ((x \<^bold>= y) \<^bold>\<rightarrow> (\<^bold>\<not> (\<^bold>\<exists>z::\<mu>. ( (z \<^bold>\<noteq> x) \<^bold>\<and> ( \<^bold>L((\<^bold>\<exists>v::\<mu>. (v \<^bold>= x) ) \<^bold>\<rightarrow> (\<^bold>\<exists>v. (v \<^bold>= z) ))      ))))) "  

(*D1 has mismatched parentheses and isn\<acute>t a proper definition; This is the best guess what it should mean.*)    
axiomatization where D1: "\<lfloor>((K x x) \<^bold>\<and> (\<^bold>\<not> (\<^bold>\<exists>y. ( (x \<^bold>\<noteq> y) \<^bold>\<and> (K y x)))) ) \<^bold>\<leftrightarrow> (\<^bold>L (\<^bold>\<exists>y. (y \<^bold>= x)))\<rfloor>"  
abbreviation D3::"\<mu>\<Rightarrow>\<sigma>"("S_") where "(S x) \<equiv> ((I x x) \<^bold>\<and> (C x x))"  
abbreviation D4a::"\<mu>\<Rightarrow>\<sigma>"("A_") where "(A x) \<equiv> (\<^bold>\<exists>y. (S y) \<^bold>\<and> (I x y) \<^bold>\<and> (C x y) \<^bold>\<and> (I y x) \<^bold>\<and> (C y x))"  
abbreviation D4b:: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("A_ _") where "(A (x::\<mu>) (y::\<mu>)) \<equiv> ((A x) \<^bold>\<and> (C y x))"  
abbreviation D2::"\<mu> \<Rightarrow> \<sigma>"("F_") where  "(F x) \<equiv> (\<^bold>\<exists>y. (((y \<^bold>\<noteq> x) \<^bold>\<and> (L y x)) \<^bold>\<and> (\<^bold>\<forall>(z::\<mu>). (((A z x) \<^bold>\<leftrightarrow> (A z y))))))"  
abbreviation D5a:: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" ("M_ _") where "(M x y) \<equiv> (((x \<^bold>\<noteq> y) \<^bold>\<and> (I x y)) \<^bold>\<and> (C x y))"
abbreviation D5b::"\<mu>\<Rightarrow>\<sigma>"("M_") where "(M x) \<equiv> (\<^bold>\<exists>y. ((S y) \<^bold>\<and> (M x y)))"  
abbreviation D6::"\<mu>\<Rightarrow>\<sigma>"("G_") where "(G x) \<equiv> ((S x) \<^bold>\<leftrightarrow> (\<^bold>\<forall>y. ((A y) \<^bold>\<rightarrow> (A y x))))"  
abbreviation D7a::"\<mu>\<Rightarrow>\<sigma>"("B_") where "(B x) \<equiv> ((K x x) \<^bold>\<and> (\<^bold>\<not>(\<^bold>\<exists>y. ((y \<^bold>\<noteq> x) \<^bold>\<and> (K y x)))))"  
abbreviation D7b:: "\<mu> \<Rightarrow> \<sigma>" ("N_") where "(N x) \<equiv>  (\<^bold>\<exists>y. (y \<^bold>\<noteq> x) \<^bold>\<and> (K y x))"
abbreviation D8::"\<mu>\<Rightarrow>\<sigma>"("E_") where "(E x) \<equiv> (\<^bold>L (\<^bold>\<exists>y. (y \<^bold>= x)))"  

section "Axioms"  

axiomatization where A1: "\<lfloor>(I x x) \<^bold>\<or> (\<^bold>\<exists>y. (y \<^bold>\<noteq> x \<^bold>\<and> (I x y)))\<rfloor>"  
axiomatization where A2: "\<lfloor>(\<^bold>\<not>(\<^bold>\<exists>y. (y \<^bold>\<noteq> x \<^bold>\<and> (C x y)))) \<^bold>\<leftrightarrow> (C x x)\<rfloor>"  
axiomatization where A3: "\<lfloor>((K y x) \<^bold>\<rightarrow> (\<^bold>N(\<^bold>\<exists>v. (v \<^bold>= x)))) \<^bold>\<leftrightarrow> (\<^bold>\<exists>v.(v \<^bold>= x))\<rfloor>"    
axiomatization where A4: "\<lfloor>(K x y) \<^bold>\<leftrightarrow> (C y x)\<rfloor>"    
axiomatization where A5: "\<lfloor>(\<^bold>\<not>(\<^bold>\<exists>z. (C z x y))) \<^bold>\<leftrightarrow> ((\<^bold>\<not>(C x y)) \<^bold>\<and> (\<^bold>\<not>(C y x)))\<rfloor>"    
axiomatization where A6: "\<lfloor>(K (x::\<mu>)) \<^bold>\<rightarrow> ((T x) \<^bold>\<leftrightarrow> (\<^bold>\<exists>y. ((O y x) \<^bold>\<and> (H x y))))\<rfloor>" 
axiomatization where A7: "\<lfloor>(\<^bold>M(\<^bold>\<not>(\<^bold>\<exists>y. (y \<^bold>= x)))) \<^bold>\<leftrightarrow> (\<^bold>\<not> \<^bold>L(\<^bold>\<exists>y. (y \<^bold>= x)))\<rfloor>"
  
subsubsection "Supposedly suppressed axioms"  
axiomatization where A8: "\<lfloor>(I x y) \<^bold>\<rightarrow> (C x y)\<rfloor>"  
axiomatization where A9: "\<lfloor>\<^bold>\<exists>y::\<mu>. (A y (x::\<mu>))\<rfloor>"  
axiomatization where A10: "\<lfloor>(D x y z) \<^bold>\<rightarrow> \<^bold>M(\<^bold>\<not>(\<^bold>\<exists>w. (w \<^bold>= x)))\<rfloor>"
axiomatization where A11: "\<lfloor>((S x) \<^bold>\<and> (L y x)) \<^bold>\<rightarrow> (S y)\<rfloor>" 
axiomatization where A12: "\<lfloor>\<^bold>\<exists>y. ((M x y) \<^bold>\<rightarrow> (M x))\<rfloor>"
axiomatization where A13: "\<lfloor>\<^bold>M (\<^bold>\<exists>x. (G x))\<rfloor>"  
axiomatization where A14: "\<lfloor>(\<^bold>N(\<^bold>\<exists>y. (y \<^bold>= x))) \<^bold>\<leftrightarrow> (\<^bold>\<not> (F x))\<rfloor>"  
text "For the next axiom we introduce a subscripted equality symbol and a new type for \<acute>time\<acute>"
typedecl t (*Type for time*) 
consts   eqtime::"'a \<Rightarrow> t \<Rightarrow> 'a \<Rightarrow> \<sigma>" ("_ \<^bold>=\<^sub>_ _") 
axiomatization where A15: "\<lfloor>(\<^bold>\<not> (G x)) \<^bold>\<rightarrow> ( ((\<^bold>\<not> \<^bold>L (\<^bold>\<exists>y. (y\<^bold>= x) )) \<^bold>\<and> (\<^bold>N (\<^bold>\<exists>y. (y \<^bold>= x)))  ) \<^bold>\<leftrightarrow> (\<^bold>\<forall>t::t. (y \<^bold>=\<^sub> t x))  )\<rfloor>"  
(*uses time variables*)
axiomatization where A16: "\<lfloor>(\<^bold>\<exists>z::\<mu>. ((A z x) \<^bold>\<and> (A z y)) ) \<^bold>\<rightarrow> (\<^bold>\<exists>z. (C z x y))\<rfloor>"  
axiomatization where A17a: "\<lfloor>(U x) \<^bold>\<rightarrow> (\<^bold>\<not>(A x))\<rfloor>"  
axiomatization where A17b: "\<lfloor>(W x) \<^bold>\<rightarrow> (\<^bold>\<not>(A x))\<rfloor>"  
axiomatization where A17c: "\<lfloor>(D (x::\<mu>)) \<^bold>\<rightarrow> (\<^bold>\<not>(A x))\<rfloor>"  
axiomatization where A17d: "\<lfloor>(J x) \<^bold>\<rightarrow> (\<^bold>\<not>(A x))\<rfloor>"  
axiomatization where A18: "\<lfloor>((S x) \<^bold>\<and> (S y)) \<^bold>\<rightarrow> ( (R x y) \<^bold>\<rightarrow> (V x y))\<rfloor>"  
axiomatization where A19: "\<lfloor>((I x y) \<^bold>\<and> (C x y) \<^bold>\<and> (I y x) \<^bold>\<and> (C y x)) \<^bold>\<leftrightarrow> (P x y)\<rfloor>"  

section "Derived Premises"  

lemma DP1: "\<lfloor>(S x) \<^bold>\<leftrightarrow> (I x x)\<rfloor>" (*using A8 by auto*) using A4 D1 by auto
lemma DP2: "\<lfloor>(C x x) \<^bold>\<rightarrow> (I x x)\<rfloor>" using A2 A8 by blast
lemma DP3: "\<lfloor>(S x) \<^bold>\<rightarrow> (A x)\<rfloor>"  by blast
lemma DP4: "\<lfloor>(S x) \<^bold>\<rightarrow> (C x x)\<rfloor>" by simp
lemma DP5: "\<lfloor>(S x) \<^bold>\<or> (M x)\<rfloor>" using A4 D1 DP2 by auto
lemma DP6: "\<lfloor>\<^bold>\<not>((S x) \<^bold>\<and> (M x))\<rfloor>" by auto
lemma DP7: "\<lfloor>((A x y) \<^bold>\<and> (S y)) \<^bold>\<rightarrow> (x \<^bold>=y)\<rfloor>" by simp
      
section "Postulates"
  
lemma P1: "\<lfloor>((M (x::\<mu>) (y::\<mu>)) \<^bold>\<and> (S y)) \<^bold>\<rightarrow> ((I x y) \<^bold>\<and> (I y y))\<rfloor>" by meson
lemma P2: "\<lfloor>((S x) \<^bold>\<and>(S y) \<^bold>\<and> (x \<^bold>\<noteq> y)) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<exists>z. (C z x y)))\<rfloor>" by (metis)    
lemma P3: "\<lfloor>(\<^bold>\<not>(\<^bold>\<exists>z. (C z x y))) \<^bold>\<rightarrow> ((\<^bold>\<not>(K x y)) \<^bold>\<and> (\<^bold>\<not> (K y x)))\<rfloor>" using A4 A5 by auto
lemma P4: "\<lfloor>(x \<^bold>\<noteq> y) \<^bold>\<rightarrow> (\<^bold>\<exists>z zz. ( ((((( (A z x) \<^bold>\<and> (A zz x) ) \<^bold>\<and> (z \<^bold>\<noteq> zz) ) \<^bold>\<or> (( (A z x) \<^bold>\<and> (z \<^bold>= x) ) \<^bold>\<and> (M y) )) \<^bold>\<or> (( (A zz y) \<^bold>\<and> (zz \<^bold>= y) ) \<^bold>\<and> (M x) )) \<^bold>\<or> ( (M x) \<^bold>\<and> (M y) )) ) )\<rfloor>" using A4 A8 D1 by fastforce
lemma P5: "\<lfloor>((S x) \<^bold>\<and> (S y) \<^bold>\<and> (x \<^bold>\<noteq> y)) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<exists>w::\<mu>. ((A w x) \<^bold>\<and> (A w y))))\<rfloor>" by (metis)
lemma P6: "\<lfloor>((S x ) \<^bold>\<and> (S y ) \<^bold>\<and> (x \<^bold>\<noteq> y)) \<^bold>\<rightarrow> (\<^bold>\<not>( (K x y)  \<^bold>\<and> (\<^bold>\<not>(K y x))))\<rfloor>" by blast
lemma P6c: "\<lfloor>(S x) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<exists>y. ((y \<^bold>\<noteq> x) \<^bold>\<and> (K y x))))\<rfloor>"  by auto
lemma P7: "\<lfloor>(S x) \<^bold>\<rightarrow> (\<^bold>L (\<^bold>\<exists>y. (y \<^bold>= x)))\<rfloor>" by simp
lemma P8: "\<lfloor>(S x) \<^bold>\<rightarrow> \<^bold>\<not>( F x)\<rfloor>" (*using A14 by blast *) by (meson A11 P5) (*both work*)
lemma P9: "\<lfloor>((S x) \<^bold>\<and> (S y)) \<^bold>\<rightarrow> ((R x y) \<^bold>\<rightarrow> (V x y))\<rfloor>" using A18 by auto
lemma P10: "\<lfloor>(A x) \<^bold>\<rightarrow> (C x x)\<rfloor>" (* using A16 A5 by blast *) by metis
lemma P11: "\<lfloor>\<^bold>L (\<^bold>\<exists>x. (G x))\<rfloor>" using A1 A2 A4 A8 (*Probably need D1*) D1 apply auto by meson
lemma P12: "\<lfloor>(S x) \<^bold>\<rightarrow> (\<^bold>\<not> (D x y (z::\<mu>)))\<rfloor>" using A10 by auto
lemma P13: "\<lfloor>((S x) \<^bold>\<and> (\<^bold>\<forall>w. ((A w) \<^bold>\<rightarrow> (A w x)))) \<^bold>\<rightarrow> (\<^bold>\<not> (D x y (z::\<mu>)))\<rfloor>" using A10 by auto
lemma P14: "\<lfloor>\<^bold>\<exists>x. ((G x) \<^bold>\<and> (\<^bold>\<forall>y. ((S y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" apply auto by (metis (mono_tags, hide_lams) A4 A8 D1)
lemma P14a: "\<lfloor>\<^bold>\<exists>x. (\<^bold>\<forall>y. ((G y) \<^bold>\<leftrightarrow> (x \<^bold>= y)) )\<rfloor>" apply auto by (metis (mono_tags, hide_lams) A4 A8 D1)
 
(*Some Useful lemmas for the following proofs*)
lemma schmelper1: "\<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (BB x))\<rfloor> \<Longrightarrow> (\<forall>x. (\<lfloor>(BB x) \<^bold>\<rightarrow> CC x\<rfloor>)) \<Longrightarrow> \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (CC x))\<rfloor>" apply auto by blast
lemma schmelper2: "\<forall>AA BB CC. (\<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (BB x))\<rfloor> \<longrightarrow> (\<forall>x. (\<lfloor>(AA x) \<^bold>\<rightarrow> CC x\<rfloor>)) \<longrightarrow> \<lfloor>\<^bold>\<exists>x. ((CC x) \<^bold>\<and> (BB x))\<rfloor>)" apply auto by blast
lemma helper1: "\<lfloor>\<^bold>\<exists>x::\<mu>. Q x\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<forall>z. (Q z \<^bold>\<rightarrow> QQ z)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<exists>x. (Q x \<^bold>\<and> QQ x)\<rfloor>" by blast
lemma helper2: "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> QQ z)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> QQ x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" 
proof -
  {fix QQ
    assume asm: "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> QQ z)\<rfloor>"
  let ?Q = "\<lambda>x. G x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x)))"
  from P14a have aa:"\<lfloor>\<^bold>\<exists>x. ((\<^bold>\<forall>y. ((G y) \<^bold>\<leftrightarrow> (x \<^bold>= y))) \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<leftrightarrow> (x \<^bold>= y))))\<rfloor>" apply auto done   
    let ?BB = "\<lambda>x. (\<^bold>\<forall>y. ((G y) \<^bold>\<leftrightarrow> (x \<^bold>= y)))"
    let ?CC = "\<lambda>x. (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (x \<^bold>= y)))"   
    have aaa: "\<forall>x. \<lfloor>?BB x \<^bold>\<rightarrow> ?CC x\<rfloor>" by simp
    from schmelper1 have  "\<And>AA BB CC. \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (BB x))\<rfloor> \<Longrightarrow> (\<forall>x. (\<lfloor>(BB x) \<^bold>\<rightarrow> CC x\<rfloor>)) \<Longrightarrow> \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (CC x))\<rfloor>" by blast
    hence "\<And>AA BB. \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (BB x))\<rfloor> \<Longrightarrow> (\<forall>x. (\<lfloor>(BB x) \<^bold>\<rightarrow> ?CC x\<rfloor>)) \<Longrightarrow> \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (?CC x))\<rfloor>" by metis (*slow*)
    hence "\<And>AA. \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (?BB x))\<rfloor> \<Longrightarrow> (\<forall>x. (\<lfloor>(?BB x) \<^bold>\<rightarrow> ?CC x\<rfloor>)) \<Longrightarrow> \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (?CC x))\<rfloor>" by presburger (*horribly slow*)
    hence  "\<And>AA. \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (?BB x))\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (?CC x))\<rfloor>" using aaa by presburger (*5s*)
    hence   "\<forall>AA. \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (?BB x))\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. ((AA x) \<^bold>\<and> (?CC x))\<rfloor>" apply auto done
    hence "\<lfloor>\<^bold>\<exists>x. ((?BB x) \<^bold>\<and> (?BB x))\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. ((?BB x) \<^bold>\<and> (?CC x))\<rfloor>" by (rule_tac x = "?BB" in allE)
    hence bl1: "\<lfloor>\<^bold>\<exists>x. ((?BB x) \<^bold>\<and> (?CC x))\<rfloor>" using aa by fast
    let ?CCC = "\<lambda>x. G x \<^bold>\<and> QQ x"
    from schmelper2 have "\<forall>BB CC. (\<lfloor>\<^bold>\<exists>x. ((?BB x) \<^bold>\<and> (BB x))\<rfloor> \<longrightarrow> (\<forall>x. (\<lfloor>(?BB x) \<^bold>\<rightarrow> CC x\<rfloor>)) \<longrightarrow> \<lfloor>\<^bold>\<exists>x. ((CC x) \<^bold>\<and> (BB x))\<rfloor>)"  by (rule_tac x = "?BB" in allE)
    hence "\<forall>CC. (\<lfloor>\<^bold>\<exists>x. ((?BB x) \<^bold>\<and> (?CC x))\<rfloor> \<longrightarrow> (\<forall>x. (\<lfloor>(?BB x) \<^bold>\<rightarrow> CC x\<rfloor>)) \<longrightarrow> \<lfloor>\<^bold>\<exists>x. ((CC x) \<^bold>\<and> (?CC x))\<rfloor>)"  by (rule_tac x = "?CC" in allE)
    hence "(\<lfloor>\<^bold>\<exists>x. ((?BB x) \<^bold>\<and> (?CC x))\<rfloor> \<longrightarrow> (\<forall>x. (\<lfloor>(?BB x) \<^bold>\<rightarrow> ?CCC x\<rfloor>)) \<longrightarrow> \<lfloor>\<^bold>\<exists>x. ((?CCC x) \<^bold>\<and> (?CC x))\<rfloor>)"  by (rule_tac x = "?CCC" in allE)
    hence bl2: " (\<forall>x. (\<lfloor>(?BB x) \<^bold>\<rightarrow> ?CCC x\<rfloor>)) \<longrightarrow> \<lfloor>\<^bold>\<exists>x. ((?CCC x) \<^bold>\<and> (?CC x))\<rfloor>" using bl1 by fast
    have "(\<forall>x. (\<lfloor>(?BB x) \<^bold>\<rightarrow> ?CCC x\<rfloor>))" using asm by presburger
    hence bl3: "\<lfloor>\<^bold>\<exists>x. ((?CCC x) \<^bold>\<and> (?CC x))\<rfloor>" using bl2 by argo
    hence " \<lfloor>\<^bold>\<exists>x. ((G x \<^bold>\<and> QQ x) \<^bold>\<and> ?CC x)\<rfloor>" by blast
    hence " \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> QQ x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" apply simp apply auto by metis (*slow*)}
  thus "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> QQ z)\<rfloor> \<Longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> QQ x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by presburger
  qed         
lemma helper3: "\<forall>QQ. (\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> QQ z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> QQ x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>)" (*useful for of nat. ded. calculus*)
  using helper2 by blast   
lemma helper4: "\<forall>QQ AA BB. (\<lfloor>\<^bold>\<forall>x. (QQ x) \<^bold>\<rightarrow> (AA x)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>x. (QQ x) \<^bold>\<rightarrow> (BB x)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>x. (QQ x) \<^bold>\<rightarrow> (AA x \<^bold>\<and> BB x)\<rfloor>)" by blast
  
lemma P15: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> (\<^bold>\<forall>x.(C x g \<^bold>\<and> I x g) )  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
  let ?form1 = "\<lambda>g. (\<^bold>\<forall>x.(C x g))"
  let ?form2 = "\<lambda>g. (\<^bold>\<forall>x.(I x g))"
  let ?form = "\<lambda>g. (\<^bold>\<forall>x.(C x g) \<^bold>\<and> (I x g))"
  let ?formstupid = "\<lambda>g. (\<^bold>\<forall>x.(C x g)) \<^bold>\<and> (\<^bold>\<forall>x.(I x g))"
  have a1: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form1 g\<rfloor>" using A2 A4 A8 D1 apply auto done
  have a2:"\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form2 g\<rfloor>" using A4 D1 DP2 A8 by auto
  from helper4 have "\<forall>AA BB. (\<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (AA x)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (BB x)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (AA x \<^bold>\<and> BB x)\<rfloor>)" by auto
  hence "\<forall>BB. (\<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (?form1 x)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (BB x)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (?form1 x \<^bold>\<and> BB x)\<rfloor>)" by (rule_tac x = "?form1" in allE)
  hence " (\<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (?form1 x)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (?form2 x)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (?form1 x \<^bold>\<and> ?form2 x)\<rfloor>)" by (rule_tac x = "?form2" in allE)      
  hence  "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> (?form1 g \<^bold>\<and> ?form2 g)\<rfloor>" using a1 a2 by fast
  hence z: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> (?formstupid g)\<rfloor>" by blast  
  have stupid: "\<forall>AA BB. (\<lambda>x. (\<^bold>\<forall>g. AA x g) \<^bold>\<and> (\<^bold>\<forall>g. BB x g)) = (\<lambda>x. (\<^bold>\<forall>g. AA x g \<^bold>\<and> BB x g))" by auto
  hence "?form = ?formstupid" by auto
  hence "\<forall>AA. (\<lfloor>\<^bold>\<forall>g. AA g \<^bold>\<rightarrow> ?formstupid g\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>g. AA g \<^bold>\<rightarrow> ?form g\<rfloor>)" by blast    
  hence "\<lfloor>\<^bold>\<forall>g. (G g) \<^bold>\<rightarrow> ?formstupid g\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<forall>g. (G g) \<^bold>\<rightarrow> ?form g\<rfloor>" by (rule_tac x = "D6" in allE)
  hence a: "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor>" using z by argo
  from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
  thus ?thesis using a by blast
qed   
lemma P16: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> (\<^bold>\<forall>x. (K g x))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
  let ?form = "\<lambda>g. (\<^bold>\<forall>x. (K g x))"  
  have a: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form g\<rfloor>" using A2 A4 A8 D1 apply auto done
  from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
  thus ?thesis using a by blast
qed         

lemma P17: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> ((\<^bold>\<not>(\<^bold>\<exists>x.((\<^bold>\<not>(I x g)) \<^bold>\<and> (K x g)))) \<^bold>\<and> (\<^bold>\<forall>x. (K g x)))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
  let ?form = "\<lambda>g. ((\<^bold>\<not>(\<^bold>\<exists>x.((\<^bold>\<not>(I x g)) \<^bold>\<and> (K x g)))) \<^bold>\<and> (\<^bold>\<forall>x. (K g x)))"  
  have a: "\<lfloor>\<^bold>\<forall>g. (G g) \<^bold>\<rightarrow> ?form g\<rfloor>" using A2 A4 A8 D1 apply auto done
  from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
  thus ?thesis using a by blast
qed  
lemma P17c2: "\<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ((B x) \<^bold>\<and> (\<^bold>\<forall>z. ((B z) \<^bold>\<rightarrow> (x \<^bold>= z))))  \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (x \<^bold>= y))))\<rfloor>" 
proof -
  have a: "\<lfloor>G x \<^bold>\<rightarrow>  ((B x) \<^bold>\<and> (\<^bold>\<forall>z. ((B z) \<^bold>\<rightarrow> (x \<^bold>= z))))\<rfloor>"  using A4 D1 DP2 by auto
  from P14 have b: "\<lfloor>\<^bold>\<exists>x. (G x)\<rfloor>" using A4 D1 DP2 by auto  
  hence b: "\<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ((B x) \<^bold>\<and> (\<^bold>\<forall>z. ((B z) \<^bold>\<rightarrow> (x \<^bold>= z)))))\<rfloor>" using a A4 D1 DP2 by auto
  thus ?thesis using A4 D1 DP2 by auto
qed
lemma P18: "\<lfloor>\<^bold>\<exists>x. ((G x) \<^bold>\<and> (\<^bold>\<forall>z. ((I z x) \<^bold>\<leftrightarrow> (K x z)) )  \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" 
proof -
  have  "\<lfloor>\<^bold>\<forall>z. (I z x \<^bold>\<leftrightarrow> (K x z))\<rfloor>"  by (metis A4 D1 DP2)
  hence a: "\<lfloor>\<^bold>\<forall>x. (G x) \<^bold>\<rightarrow> (\<^bold>\<forall>z.(I z x \<^bold>\<leftrightarrow> (K x z)))\<rfloor>" apply auto apply metis              
    apply metis apply metis apply metis apply metis apply metis 
    apply metis apply metis apply metis apply metis apply metis done (*No idea what\<acute>s going on here.*)
  let ?QQ = "\<lambda>x. (\<^bold>\<forall>z.(I z x \<^bold>\<leftrightarrow> (K x z)))"   
  from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?QQ z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?QQ x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?QQ" in allE)
  hence "\<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?QQ x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" using a by blast
  hence "\<lfloor>\<^bold>\<exists>x. ((G x) \<^bold>\<and> (\<^bold>\<forall>z.((I z x) \<^bold>\<leftrightarrow> (K x z))) \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" apply auto done  
  thus "\<lfloor>\<^bold>\<exists>x. ((G x) \<^bold>\<and> (\<^bold>\<forall>z. ((I z x) \<^bold>\<leftrightarrow> (K x z)) )  \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by blast
qed      
lemma P19: "\<lfloor>(\<^bold>\<exists>x. ((G x) \<^bold>\<and> (E x)  \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))) \<^bold>\<and> (\<^bold>\<forall>x.(A x \<^bold>\<rightarrow> E x))\<rfloor>" 
proof -
  have sc: "\<lfloor>\<^bold>\<forall>x.(A x \<^bold>\<rightarrow> E x)\<rfloor>" by simp
  have fr: "\<lfloor>(\<^bold>\<exists>x. ((G x) \<^bold>\<and> (E x)  \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x)))))\<rfloor>"
   proof -
      have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> E z)\<rfloor>" by simp
      thus ?thesis using helper3 by fastforce (*slow*) qed
  thus ?thesis using sc by presburger
qed        
lemma P20: "\<lfloor>\<^bold>\<exists>x. ((G x) \<^bold>\<and> (\<^bold>\<forall>y. ((A y) \<^bold>\<rightarrow> (x \<^bold>= y)))  \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" 
proof -
  have a: "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> (\<^bold>\<forall>y. ((A y) \<^bold>\<rightarrow> (z \<^bold>= y))))\<rfloor>" by force
  let ?QQ = "\<lambda>x. (\<^bold>\<forall>y. ((A y) \<^bold>\<rightarrow> (x \<^bold>= y)))"      
  from helper3 have "(\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?QQ z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?QQ x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>)" by (rule_tac x = "?QQ" in allE)   
  thus ?thesis using a by blast
qed      
lemma P21: "\<lfloor>\<^bold>\<exists>g::\<mu>. ((G g) \<^bold>\<and> ((\<^bold>\<forall>x::\<mu>. (\<^bold>\<exists>y::\<mu>.((( (A y g) \<^bold>\<and> (\<^bold>\<not>(x \<^bold>= g))) \<^bold>\<and> (K y x)) \<^bold>\<and> (\<^bold>\<not> (\<^bold>\<exists>z.((\<^bold>\<not>(z \<^bold>= y)) \<^bold>\<and> (K z x)))
\<^bold>\<rightarrow> ((\<^bold>\<forall>t::t. ( (\<^bold>\<exists>v::\<mu>. (v \<^bold>=\<^sub> t x)) \<^bold>\<and> (\<^bold>N (\<^bold>\<exists>v::\<mu>. (v \<^bold>= x)))))) \<^bold>\<and> (\<^bold>\<not>(F x)) )) ) ))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
 nitpick[user_axioms] (*nitpick finds a counterexample*) (*Typo somewhere? Typo in Jarret\<acute>s text?*)
oops
  
(*lemma P22: There is an operator missing; I\<acute>m not 100% sure how it should be read for it to be a theorem *) 
lemma P23: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> (\<^bold>\<forall>x. ((\<^bold>N(\<^bold>\<exists>v.(v \<^bold>= x))) \<^bold>\<rightarrow> (\<^bold>\<exists>y.((A y g) \<^bold>\<and> (\<^bold>N ((\<^bold>\<exists>v. (v \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>v. (v \<^bold>= x))))))))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
  let ?form = "\<lambda>g. (\<^bold>\<forall>x. ((\<^bold>N(\<^bold>\<exists>v.(v \<^bold>= x))) \<^bold>\<rightarrow> (\<^bold>\<exists>y.((A y g) \<^bold>\<and> (\<^bold>N ((\<^bold>\<exists>v. (v \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>v. (v \<^bold>= x))))))))"
  have a: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((\<^bold>N(\<^bold>\<exists>v.(v \<^bold>= x))) \<^bold>\<rightarrow> (\<^bold>\<exists>y.((A y g) \<^bold>\<and> (\<^bold>N ((\<^bold>\<exists>v. (v \<^bold>= y)) \<^bold>\<rightarrow> (\<^bold>\<exists>v. (v \<^bold>= x))))))))\<rfloor>" apply auto 
    apply metis apply metis apply metis apply metis done (*I\<acute>m so sorry :/*)
  from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
  thus ?thesis using a by fast
qed
lemma P24: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> (\<^bold>\<forall>x.(((\<^bold>\<not>(x \<^bold>= g)) \<^bold>\<and> (K g x)) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>L(\<^bold>\<exists>y. (y \<^bold>= x))))))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>"
proof -
  let ?form = "\<lambda>g. (\<^bold>\<forall>x::\<mu>.(((\<^bold>\<not>(x \<^bold>= g)) \<^bold>\<and> (K g x)) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>L(\<^bold>\<exists>y. (y \<^bold>= x))))))"
  have a: "\<lfloor>\<^bold>\<forall>g. (G g) \<^bold>\<rightarrow> (\<^bold>\<forall>x::\<mu>.(((\<^bold>\<not>(x \<^bold>= g)) \<^bold>\<and> (K g x)) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>L(\<^bold>\<exists>y. (y \<^bold>= x))))))\<rfloor>" 
  proof -
    have "\<forall>m ma mb. \<exists>mc md. (m::\<mu>) = ma \<or> (mc::\<mu>) \<noteq> mb \<and> md \<noteq> ma"
      by (metis (no_types))
    then show ?thesis
      by auto qed
  from helper3 have "\<lfloor>\<^bold>\<forall>z::\<mu>. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
  thus ?thesis using a by blast
qed      
(*lemma P25: SAME AS P18*)
lemma P26: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> (\<^bold>\<forall>x y. (((\<^bold>\<exists>z zz. ((M y z) \<^bold>\<and> (M z zz))) \<^bold>\<and> (K x y)) \<^bold>\<rightarrow> (K g y)  ))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>"
proof -
 let ?form = "\<lambda>g. (\<^bold>\<forall>x y. (((\<^bold>\<exists>z zz. ((M y z) \<^bold>\<and> (M z zz))) \<^bold>\<and> (K x y)) \<^bold>\<rightarrow> (K g y)))" 
 have a: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form g\<rfloor>" apply auto apply metis apply metis apply metis apply metis apply metis done
 from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
 thus ?thesis using a by blast
qed  
lemma P27: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> (\<^bold>\<forall>x. (((K g x) \<^bold>\<and> (\<^bold>\<not>(\<^bold>\<exists>z. ((\<^bold>\<not>(z \<^bold>= g)) \<^bold>\<and> (K z x))))) \<^bold>\<rightarrow> (\<^bold>N (\<^bold>\<exists>v.(v \<^bold>= x))))) \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
let ?form = "\<lambda>g. (\<^bold>\<forall>x. (((K g x) \<^bold>\<and> (\<^bold>\<not>(\<^bold>\<exists>z. ((\<^bold>\<not>(z \<^bold>= g)) \<^bold>\<and> (K z x))))) \<^bold>\<rightarrow> (\<^bold>N (\<^bold>\<exists>v.(v \<^bold>= x)))))"  
have a: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form g\<rfloor>" apply auto done
from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
thus ?thesis using a by blast
qed      
lemma P28: "\<lfloor>\<^bold>\<forall>x.( ( (F x) \<^bold>\<and> (\<^bold>\<exists>t. (\<^bold>\<not>(\<^bold>\<exists>v. (v \<^bold>=\<^sub> t x))))) \<^bold>\<rightarrow>
(( (K g x) \<^bold>\<and> (\<^bold>\<forall>y. ((I x y) \<^bold>\<rightarrow> (K y x)))) \<^bold>\<and> (\<^bold>\<exists>z.(((( (\<^bold>\<not>(z \<^bold>= y)) \<^bold>\<and> (K z x)) \<^bold>\<and> (\<^bold>\<not>(\<^bold>N(\<^bold>\<exists>v. (v \<^bold>= z))))) \<^bold>\<and>
(\<^bold>\<exists>t. (\<^bold>\<not>(\<^bold>\<exists>v. (v \<^bold>=\<^sub> t z)))) \<^bold>\<and> (F z))))))\<rfloor>" using A15 A4 D1 DP2 by auto
  
lemma P29: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> ((\<^bold>L (\<^bold>\<exists>x. (x \<^bold>= g))) \<^bold>\<and> (\<^bold>\<forall>x. ((\<^bold>\<not>(x \<^bold>= g)) \<^bold>\<rightarrow> (N x))))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
  let ?form = "\<lambda>g.  ((\<^bold>L (\<^bold>\<exists>x. (x \<^bold>= g))) \<^bold>\<and> (\<^bold>\<forall>x. ((\<^bold>\<not>(x \<^bold>= g)) \<^bold>\<rightarrow> (N x))))"  
  have a: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form g\<rfloor>" apply auto apply metis apply metis apply metis apply metis done
    from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
    thus ?thesis using a by blast
  qed
lemma P30: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> (\<^bold>\<forall>x y. (((K x) \<^bold>\<and> (T x) \<^bold>\<and> (O y x)) \<^bold>\<rightarrow> ((A y) \<^bold>\<or> (M y))))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
  let ?form = "\<lambda>g. (\<^bold>\<forall>x y. (((K x) \<^bold>\<and> (T x) \<^bold>\<and> (O y x)) \<^bold>\<rightarrow> ((A y) \<^bold>\<or> (M y))))"  
  have a: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form g\<rfloor>" apply auto apply metis apply metis apply metis apply metis apply metis done   
  from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
  thus ?thesis using a by blast
qed           
lemma P31a: "\<lfloor>\<^bold>\<forall>x.((U x) \<^bold>\<rightarrow> (M x))\<rfloor>" using DP5 A9 A2 A17a by metis
lemma P31b: "\<lfloor>\<^bold>\<forall>x.((W x) \<^bold>\<rightarrow> (M x))\<rfloor>" using DP5 A9 A2 A17b by metis 
lemma P31c: "\<lfloor>\<^bold>\<forall>x.((D x) \<^bold>\<rightarrow> (M x))\<rfloor>" using DP5 A9 A2 A17c by metis 
lemma P31d: "\<lfloor>\<^bold>\<forall>x.((J x) \<^bold>\<rightarrow> (M x))\<rfloor>" using DP5 A9 A2 A17d by metis 
lemma P32: "\<lfloor>\<^bold>\<forall>x. ((W x) \<^bold>\<rightarrow> ((\<^bold>\<not>(B x)) \<^bold>\<and> (N x)))\<rfloor>" using P31b by auto
(*P33 are \<acute>not derivable in [Jarret\<acute>s] view\<acute>*) 
lemma P34: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> (\<^bold>\<forall>x. ((A x g) \<^bold>\<leftrightarrow> (P x g)))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
  let ?form = "\<lambda>g. (\<^bold>\<forall>x. ((A x g) \<^bold>\<leftrightarrow> (P x g)))"  
  have a: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form g\<rfloor>" apply auto apply metis apply (metis A19) apply metis apply metis apply metis apply metis
      apply metis apply metis apply metis apply metis apply metis apply metis apply metis apply metis apply metis apply metis apply metis apply metis apply metis apply metis done (*:/*)
  from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
  thus ?thesis using a by blast
qed          
lemma P35: "\<lfloor>\<^bold>\<exists>g. ((G g) \<^bold>\<and> ((\<^bold>L(\<^bold>\<exists>x. (x \<^bold>= g))) \<^bold>\<and> (\<^bold>\<forall>x. ((\<^bold>\<not>(x \<^bold>= g)) \<^bold>\<rightarrow> (N x))))  \<^bold>\<and> (\<^bold>\<forall>yy. ((G yy) \<^bold>\<rightarrow> (yy \<^bold>= g))))\<rfloor>" 
proof -
  let ?form = "\<lambda>g.((\<^bold>L(\<^bold>\<exists>x. (x \<^bold>= g))) \<^bold>\<and> (\<^bold>\<forall>x. ((\<^bold>\<not>(x \<^bold>= g)) \<^bold>\<rightarrow> (N x))))"  
  have a: "\<lfloor>\<^bold>\<forall>g. G g \<^bold>\<rightarrow> ?form g\<rfloor>" apply auto apply metis apply metis apply metis apply metis done  
  from helper3 have "\<lfloor>\<^bold>\<forall>z. (G z \<^bold>\<rightarrow> ?form z)\<rfloor> \<longrightarrow> \<lfloor>\<^bold>\<exists>x. (G x \<^bold>\<and> ?form x \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (y \<^bold>= x))))\<rfloor>" by (rule_tac x = "?form" in allE)
  thus ?thesis using a by blast
qed        
(*P36 is also not derivable according to Jarret*)
  
text "Nitpick confirms consistency"  
lemma True nitpick[user_axioms, satisfy, expect=genuine]
oops
end
  
