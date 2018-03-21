theory BlumMalinovich
  
  imports Main
    
begin
    
(*This automates Blum and Malinovich\<acute>s formalization of (a part of) Spinoza\<acute>s Ethics I
See: http://www.metalogicon.org/rivista/1993gg/malinovich93gg.pdf
for their paper \<acute>A Formalization of a Segment of Part I of Spinoza\<acute>s Ethics\<acute>*)  
  typedecl i (*Stuff in the world*)


section "Constants and terms"
text "Here we introduce the constants and corresponding interpretations that Blum and Malinovich use."
  
text "Axy \<equiv> x is an attribute of y"
consts A :: "i \<Rightarrow> i\<Rightarrow> bool"

text "Cxy \<equiv> x causes y"
consts C :: "i \<Rightarrow> i\<Rightarrow> bool"
  
text "Dxy \<equiv> x depends on y"   
consts D :: "i \<Rightarrow> i\<Rightarrow> bool" 

text "Ex \<equiv> x is eternal"
consts E :: "i\<Rightarrow> bool" ("E")

text "Exy \<equiv> x is the essence of y"  
consts Es :: "i \<Rightarrow> i \<Rightarrow> bool" ("E")

text "Fx \<equiv> x is finite"  
consts F :: "i\<Rightarrow> bool"

text "Hx \<equiv> x is absolutely infinite"  
consts H :: "i\<Rightarrow> bool"

text "Ixy \<equiv> x is contained in y"  
consts I :: "i \<Rightarrow> i \<Rightarrow> bool"

text "Kx \<equiv> x is finite after its kind"
consts K :: "i\<Rightarrow> bool" ("K")
 
text "Kxy \<equiv> x and y are of the same kind"  
consts Ki :: "i \<Rightarrow> i \<Rightarrow> bool" ("K") 
  
text "Lxy \<equiv> x limits y"  
consts L :: "i \<Rightarrow> i \<Rightarrow> bool"
  
text "Mxy \<equiv> x is a mode of y"  
consts M :: "i \<Rightarrow> i \<Rightarrow> bool"
  
text "Nx \<equiv> x has necessary existence"  
consts N :: "i\<Rightarrow> bool"
  
text "Pxy \<equiv> x is prior to y"  
consts P :: "i \<Rightarrow> i \<Rightarrow> bool"
  
text "Qx \<equiv> x is free"
consts Q :: "i\<Rightarrow> bool"
  
text "Sx \<equiv> x is a substance"  
consts S :: "i\<Rightarrow> bool"
                            
text "Txy \<equiv> x is the effect of y"
consts T :: "i \<Rightarrow> i \<Rightarrow> bool"
  
text "Uxy \<equiv> x knows y"  
consts U :: "i \<Rightarrow> i \<Rightarrow> bool"
 
text "Wxyz \<equiv> x and y have z in common"  
consts W :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool" 

text "Next we need a constant for \<acute>being god(like)\<acute>. Blum and Malinovich seem to have 
forgot to include it in their list (but use it in their proofs)."
consts G :: "i \<Rightarrow> bool"
  
text "Blum and Malinovich also introduce another operator that uses quine corners.
This operator is needed for only one axiom of Spinoza\<acute>s, which is in turn never used
in their proofs. Therefore, we omit the operator (and corresponding axiom) completely here"
  
section "Definitions"
text "Since not all \<acute>definitions\<acute> are in fact proper definitions in this formalization,
 we will treat all of them as axioms for consistency"
  
axiomatization where Done: "(C x x) \<equiv> (N x)"  
axiomatization where Dtwo: "(K (x::i)) \<equiv> \<exists>y. ((K x y) \<and> (L y x) \<and> (x \<noteq> y))"  
axiomatization where Dthree_a: "(S x) \<equiv> (I x x)"  
axiomatization where Dthree_b: "(S x) \<equiv> (D x x)"  
axiomatization where Dthree_c: "(S x) \<Longrightarrow> \<not> (\<exists>y. ((D x  y) \<and> (x \<noteq> y)))"  
axiomatization where Dfour_a: "(A x y) \<equiv> ((S y) \<and> (E x y))"  
axiomatization where Dfour_b: "\<exists>y. ((S x) \<longrightarrow> (A y x))"  
axiomatization where Dfive: "(M x y) \<equiv> (S y) \<and> (I x y) \<and> (x \<noteq> y) \<and> (D x y)"  
axiomatization where Dsix: "(G x) \<Longrightarrow> ((S x) \<and> (H x))"  
axiomatization where Dseven: "(Q x) \<equiv> ((N x) \<and> (C x x))"  
axiomatization where Deight: "(E x) \<equiv> (N x)"  
  
section "Axioms"
axiomatization where Ax1: "(I x x) \<or> (\<exists>y. ((x \<noteq> y) \<and> (I x y)))"
axiomatization where Ax2: "((x \<noteq> y) \<and> (D x y)) \<Longrightarrow> D x x"
axiomatization where Ax3: "(\<forall>x. (\<exists>y.((C x y) \<longrightarrow> (\<exists>z. (T z x))))) \<and> (\<forall>x. (\<exists>y. ((T x y) \<longrightarrow> (\<exists>z. (C z x)))))"
axiomatization where Ax4: "(C x y) \<Longrightarrow> (\<forall>z. ((U z y) \<longrightarrow> (U z y)))" (*this can\<acute>t be right...*)

axiomatization where Ax5: "(\<not>(\<exists>z. (W x y z))) \<Longrightarrow> ((\<exists>v.((U v x) \<and> (\<not>(U v x)) )) \<and>(\<exists>v. ((U v y) \<and> (\<not> (D x y)) \<and> (\<not> (D y x))  \<and> (\<not>(U v x)))) )"
(*Ax5 has been changed bc. it makes no sense in the orig. version.*)
(*Ax 6 missing /quine corners/irrelevant*)
  
axiomatization where Ax7: "(N x) \<Longrightarrow> (\<forall>y. ((E y x) \<longrightarrow> (\<forall>z.((A z y) \<longrightarrow> (\<exists>u. (z = u))))))" 


section "Postulates"
  
axiomatization where P1: "((x = y) \<and> (D x y)) \<Longrightarrow> (P y x)"
axiomatization where P2: "(D x x) \<equiv> (C x x)"
axiomatization where P3: "((D x y) \<or> (D y x)) \<equiv> (\<exists>w. (W x y w))" (*For some reason the authors use = here*)
axiomatization where P4: "((E u x) \<and> (E v y)) \<Longrightarrow> ((x = y) \<equiv> (u = v))"
axiomatization where P5: "(Q x) \<equiv> (\<not>(\<exists>y. (L y x)))"

section "Propositions"
  (*
lemma god: "(G x) \<Longrightarrow> (N x)" using Done Dsix Dthree_b P2 by blast
(*The axiom set may be many things, but it is certainly not minimal...*)
  *)
lemma prop1: "((S x) \<and> (M y x)) \<Longrightarrow> (P x y)" using Ax2 Dfive Dthree_b Dthree_c by blast

lemma prop2: "((S x) \<and> (S y) \<and> (\<exists>z v. ((A z x) \<and> (A v y) \<and> (z \<noteq> v)))) \<Longrightarrow> (\<not>(\<exists>w. (W x y w)))" by (metis Dfour_a Dthree_c P3 P4)
    
lemma prop3: "(\<not>(\<exists>z. (W x y z))) \<Longrightarrow> ((\<not>C x y) \<and> (\<not>(C y x)))" using Ax5 by auto 

lemma prop4: "((S x) \<and> (S y) \<and> (x \<noteq> y)) \<Longrightarrow> ((\<exists>z. ((A z x) \<and> (\<not>(A z y)))) \<or> (\<exists>v. ((M v x) \<and> (\<not>(M v y)))))" using Dfour_a Dfour_b P4 by blast
  
lemma prop5: "((S x) \<and> (S y) \<and> (x \<noteq> y)) \<Longrightarrow> (\<exists>z. (W x y z))" using Ax5 by auto
(*Probably a typo in orig. version. Changed (W s y z) to (W x y z)*)
 
lemma prop6: "((S x) \<and> (S y) \<and> (x \<noteq> y)) \<Longrightarrow> (\<not>(C x y))" by (metis Dthree_c P3 prop5)
    
lemma prop7: "(S x) \<Longrightarrow> (N x)"  by (simp add: Done Dthree_b P2)

lemma prop8: "(S x) \<Longrightarrow> ((\<not>(K x))  \<and> (\<not>(\<exists>y. (L y x))) )" using Done Dseven Dthree_b Dtwo P2 P5 by auto

lemma prop9: "(G x) \<Longrightarrow> (N x)"  by (simp add: Dsix prop7)
    
text "Nitpick confirms consistency"
lemma True nitpick[user_axioms, satisfy, expect=genuine] (*Nitpick finds a model*)
    oops

end
 