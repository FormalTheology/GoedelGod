theory Friedman

imports "../QML"

begin
(*This is an automatization of Friedman\<acute>s formalization of (a part of) Spinoza\<acute>s Ethics I.
For the corresponding paper \<acute>Was Spinoza fooled by the ontological argument?\<acute>
see: https://link.springer.com/article/10.1007%2FBF02380843*)
  
section "Constants and Terms"
  
text "x is a cause (or condition) of y"
consts C::"\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>"("C") 
  
text "x endures at y"  
consts E:: "\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>"("E")
  
text "x is a time"   
consts T::"\<mu>\<Rightarrow>\<sigma>"("T")
  
text "x is a substance"
consts S::"\<mu>\<Rightarrow>\<sigma>"("S")
  
text "x is in y" 
consts I:: "\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>"("I")
  
text "x is conceived through y"
consts V::"\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>"("V")
  
text "The knowledge of x depends upon and involves the knowledge of y"   
consts K::"\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>"("K")
  
text "x is an attribute of y"  
consts B::"\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>"("B")
  
text "x has infinitely many attributes"
consts I\<^sub>1::"\<mu>\<Rightarrow>\<sigma>"("I\<^sub>1")  (*Friedman uses just I, but
giving it a subscript makes parsing easier.*)

text "x is god"  
consts G::"\<mu>\<Rightarrow>\<sigma>"("G")

(*P\<^sub>F for arbitrary F is missing; we don\<acute>t need them here however and including them would
make parsing much more difficult*)

text "x is a possibility of substance"
consts P\<^sub>s::"\<mu>\<Rightarrow>\<sigma>"("P\<^sub>S") 
  
text "x is a possibility of absolutely infinite substance"  
consts P\<^sub>G::"\<mu>\<Rightarrow>\<sigma>"("P\<^sub>G")

text "x is a possibility of causally necessary being"  
consts P\<^sub>C::"\<mu>\<Rightarrow>\<sigma>"("P\<^sub>C")
  
text "x is a possibility of logically (metaphysically) necessary being"  
consts P\<^sub>N::"\<mu>\<Rightarrow>\<sigma>"("P\<^sub>N") 
  
text "x can be conceived as not actualized"
consts Z\<^sub>V::"\<mu>\<Rightarrow>\<sigma>"("Z\<^sub>V") 
  
text "x is an actualization of y"
consts A::"\<mu>\<Rightarrow>\<mu>\<Rightarrow>\<sigma>"("A")
  
text "x is a logically (metaphysically) necessary being"
consts N:: "\<mu>\<Rightarrow>\<sigma>" ("N") (*Friedman defines this; but it is easier to use an axiom instead; see below*)
  
section "Definitions"
text "x is a causally necessary being"  
abbreviation Def1::"\<mu>\<Rightarrow>\<sigma>" ("C\<^sub>N _") where "(C\<^sub>N x) \<equiv> (\<^bold>\<not> (\<^bold>\<exists>y. ((C y x) \<^bold>\<and> \<^bold>\<not>(y \<^bold>= x)))) \<^bold>\<and> (\<^bold>\<forall>t.((T t) \<^bold>\<rightarrow> (E x t)))"  

  
text {*Def2 is originally a metalogical definition:
"There is a 1-place formula D of the object language such that x uniquely satisfies D (that is,
D formally defines x) and \<box>\<exists>x. (D x)"
The definition used here interprets the above in HOL *}
text "x is a logically (metaphysically) necessary being"
axiomatization where Def2: "\<lfloor>(N x) \<^bold>\<leftrightarrow> (\<^bold>\<exists>D. ((D x) \<^bold>\<and> (\<^bold>\<forall>y. (D y \<^bold>\<rightarrow> (x \<^bold>= y))) \<^bold>\<and> (\<^bold>\<box> (\<^bold>\<exists>z. (D z)))))\<rfloor>"
  
section "Axioms"
text "Some of these axioms are Spinoza\<acute>s definitions (they tart with a D), some are his axioms (starting with A),
some are (supposedly) suppressed premises (S)."
  
axiomatization where S1: "\<lfloor>\<^bold>\<box> (\<^bold>\<forall>x.((C\<^sub>N x) \<^bold>\<rightarrow> (N x)))\<rfloor>"
(*Friedman: clearly questionable*)

axiomatization where S2: "\<lfloor>C y x \<^bold>\<leftrightarrow> I x y\<rfloor>"

axiomatization where D3: "\<lfloor>S x \<^bold>\<leftrightarrow> ((I x y) \<^bold>\<and> (V x x))\<rfloor>"

axiomatization where A1: "\<lfloor>(I x x) \<^bold>\<or> (\<^bold>\<exists>y. ((\<^bold>\<not>(y \<^bold>= x)) \<^bold>\<and> (I x y)))\<rfloor>"
  
axiomatization where S3: "\<lfloor>(I x x) \<^bold>\<rightarrow> (\<^bold>\<forall>t. ((T t) \<^bold>\<rightarrow> (E x t)))\<rfloor>"

axiomatization where A7: "\<lfloor>(P\<^sub>N x) \<^bold>\<rightarrow> \<^bold>\<not> (Z\<^sub>V x)\<rfloor>"

axiomatization where D6: "\<lfloor>G x \<^bold>\<leftrightarrow> (S x) \<^bold>\<and> (I\<^sub>1 x) \<^bold>\<and> (\<^bold>\<forall>y. (\<^bold>\<exists>z. ((B y z) \<^bold>\<rightarrow> (B y x))))\<rfloor>"  

axiomatization where S4: "\<lfloor>\<^bold>\<exists>x. (P\<^sub>G x)\<rfloor>"  


text "The following Axioms are a schema in Friedman\<acute>s paper. The easiest way is however,
to use those instantiations that are actually needed. These are reproduced below"  
(*There might be more efficient encodings, but this one is easiest on the provers.*)  
axiomatization where S5a1: "\<lfloor>(\<^bold>\<forall>x. ((S x) \<^bold>\<rightarrow> (S x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>S x) \<^bold>\<rightarrow> (P\<^sub>S x)))\<rfloor>"
axiomatization where S5a2: "\<lfloor>(\<^bold>\<forall>x. ((S x) \<^bold>\<rightarrow> (G x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>S x) \<^bold>\<rightarrow> (P\<^sub>G x)))\<rfloor>"
axiomatization where S5a3: "\<lfloor>(\<^bold>\<forall>x. ((S x) \<^bold>\<rightarrow> (N x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>S x) \<^bold>\<rightarrow> (P\<^sub>N x)))\<rfloor>"

axiomatization where S5b1: "\<lfloor>(\<^bold>\<forall>x. ((G x) \<^bold>\<rightarrow> (S x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>G x) \<^bold>\<rightarrow> (P\<^sub>S x)))\<rfloor>"
axiomatization where S5b2: "\<lfloor>(\<^bold>\<forall>x. ((G x) \<^bold>\<rightarrow> (G x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>G x) \<^bold>\<rightarrow> (P\<^sub>G x)))\<rfloor>"
axiomatization where S5b3: "\<lfloor>(\<^bold>\<forall>x. ((G x) \<^bold>\<rightarrow> (N x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>G x) \<^bold>\<rightarrow> (P\<^sub>N x)))\<rfloor>"
  
axiomatization where S5c1: "\<lfloor>(\<^bold>\<forall>x. ((N x) \<^bold>\<rightarrow> (S x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>N x) \<^bold>\<rightarrow> (P\<^sub>S x)))\<rfloor>"
axiomatization where S5c2: "\<lfloor>(\<^bold>\<forall>x. ((N x) \<^bold>\<rightarrow> (G x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>N x) \<^bold>\<rightarrow> (P\<^sub>G x)))\<rfloor>"
axiomatization where S5c3: "\<lfloor>(\<^bold>\<forall>x. ((N x) \<^bold>\<rightarrow> (N x))) \<^bold>\<rightarrow> (\<^bold>\<forall>x. ((P\<^sub>N x) \<^bold>\<rightarrow> (P\<^sub>N x)))\<rfloor>"
  
axiomatization where S6: "\<lfloor>(\<^bold>\<not>(Z\<^sub>V xx)) \<^bold>\<rightarrow> (\<^bold>\<exists>x. (A x xx ))\<rfloor>" 
  
axiomatization where S7a: "\<lfloor>((P\<^sub>S xx) \<^bold>\<and> (A x xx)) \<^bold>\<rightarrow> (S x)\<rfloor>"  
axiomatization where S7b: "\<lfloor>((P\<^sub>G xx) \<^bold>\<and> (A x xx)) \<^bold>\<rightarrow> (G x)\<rfloor>"  
axiomatization where S7c: "\<lfloor>((P\<^sub>N (xx::\<mu>)) \<^bold>\<and> (A x xx)) \<^bold>\<rightarrow> (N x)\<rfloor>"  

axiomatization where S8: "\<lfloor>(S x) \<^bold>\<rightarrow> (\<^bold>\<exists>w. (B w x))\<rfloor>"

axiomatization where S9: "\<lfloor>((B w x) \<^bold>\<and> (B w y)) \<^bold>\<rightarrow> (V x y)\<rfloor>"  
  
axiomatization where S10: "\<lfloor>(V x x) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<exists>y. (V x y) \<^bold>\<and> \<^bold>\<not>(x \<^bold>= y)))\<rfloor>"  

text {*Friedman frequently references Spinoza\<acute>s fourth axiom but never states if formally.
It follows from the paper that Friedman thinks the following axiom must follow from A4.*}
(* nitpick confirms another axiom is necessary for the following proof of P6.*)
  
axiomatization where possA4: "\<lfloor>C y x \<^bold>\<leftrightarrow> K x y\<rfloor>" (*See step3 p.326*)
  
(*There are also other suppressed premises that are not in Friedman\<acute>s list*)  
  
axiomatization where S11: "\<lfloor>K x y \<^bold>\<rightarrow> V x y\<rfloor>"  
  
  
section "Postulates"  
lemma P6: "\<lfloor>\<^bold>\<box> (\<^bold>\<forall>x. ((S x) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists>y. ((\<^bold>\<not>(y \<^bold>= x)) \<^bold>\<and> (C y x)))))\<rfloor>" by (metis S10 S11 S8 S9 possA4)

lemma P7a: "\<lfloor>\<^bold>\<box> (\<^bold>\<forall>x. ((S x) \<^bold>\<rightarrow> (C\<^sub>N x)))\<rfloor>" using D3 P6 S3 by blast
    
lemma P7b: "\<lfloor>\<^bold>\<box> (\<^bold>\<forall>x. (S x \<^bold>\<rightarrow> N x))\<rfloor>" by (simp add: P7a S1)

(*For the next lemma we need \<box>P \<Rightarrow> P*)    
axiomatization where T: "reflexive"    
    
lemma P11a: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>x. (G x))\<rfloor>" 
proof -
  have "\<lfloor>\<^bold>\<exists>x. P\<^sub>G x\<rfloor>" by (simp add: S4)
  from P7b T have "\<lfloor>(\<^bold>\<forall>x. (S x \<^bold>\<rightarrow> N x))\<rfloor>" by metis
  hence "\<lfloor>\<^bold>\<forall>x. (P\<^sub>S x) \<^bold>\<rightarrow> (P\<^sub>N x)\<rfloor>"using S5a3 by simp  
  hence "\<lfloor>P\<^sub>S xx \<^bold>\<rightarrow> (\<^bold>\<exists>x. A x xx)\<rfloor>" by (simp add: A7 S6)
  hence "\<lfloor>\<^bold>\<exists>xx. P\<^sub>G xx \<^bold>\<and> (\<^bold>\<exists>x. (A x xx))\<rfloor>" by (meson A7 D6 S4 S5b1 S6 \<open>\<lfloor>(\<lambda>w. \<forall>x. (P\<^sub>S x \<^bold>\<rightarrow> P\<^sub>N x) w)\<rfloor>\<close>)    
  hence "\<lfloor>\<^bold>\<exists>x xx. (P\<^sub>G xx \<^bold>\<and> (A x xx))\<rfloor>" by blast
  hence "\<lfloor>\<^bold>\<exists>x. G x\<rfloor>" using S7b by blast
  thus ?thesis by simp
qed      

lemma P11b: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists>x. (G x) \<^bold>\<and> (\<^bold>\<forall>y. ((G y) \<^bold>\<rightarrow> (x \<^bold>= y))))\<rfloor>"  by (meson D3 D6 P11a P6 S2)
 
text "Nitpick confirms consistency"    
lemma True nitpick[user_axioms, satisfy, expect=genuine] (*Nitpick finds a model*)
oops    
end