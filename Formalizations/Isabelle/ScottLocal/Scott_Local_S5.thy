theory Scott_Local_S5 imports QML_Local_Const 
begin
 declare [[smt_solver = cvc4]]

  consts P :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"                                     (* Positive *)

  axiomatization where 
(* A1: Either a property or its negation is positive, but not both *)
   A1a: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>P(\<Phi>)\<rfloor>\<^sup>c\<^sup>w" and 
   A1b: "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<not>P(\<Phi>) \<^bold>\<rightarrow> P(\<^sup>\<not>\<Phi>)\<rfloor>\<^sup>c\<^sup>w" and 
(* A2: A property necessarily implied by a positive property is positive *)
   A2: "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>. P(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> P(\<Psi>)\<rfloor>\<^sup>c\<^sup>w"

(* T1: Positive properties are possibly exemplified *)
 theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>x. \<Phi>(x))\<rfloor>\<^sup>c\<^sup>w" using A1a A2 by blast

(* God: A God-like being possesses all positive properties *)
 definition G where "G(x) = (\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"   

(* A3: The property of being God-like is positive *)
 axiomatization where A3: "\<lfloor>P(G)\<rfloor>\<^sup>c\<^sup>w"

(* C: Possibly, God exists *) 
 corollary C: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G(x))\<rfloor>\<^sup>c\<^sup>w" by (metis A3 T1)

(* A4: Positive properties are necessarily positive *)
 axiomatization where A4: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<box>(P(\<Phi>))\<rfloor>\<^sup>c\<^sup>w" 

(* Ess: An essence of an individual is a property possessed by 
        it and necessarily implying any of its properties: *)
 definition ess (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi>(x) \<^bold>\<and> (\<^bold>\<forall>\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y)))"

(* T2: Being God-like is an essence of any God-like being *)
 theorem T2: "\<lfloor>\<^bold>\<forall>x. G(x) \<^bold>\<rightarrow> G ess x\<rfloor>\<^sup>c\<^sup>w" by (smt A1b A4 G_def ess_def)

(* NE: Necessary existence of an individual is the necessary 
       exemplification of all its￼essences *)
 definition NE where "NE(x) = (\<^bold>\<forall>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>x. \<Phi>(x)))"

(* A5: Necessary existence is a positive property *)
 axiomatization where A5:  "\<lfloor>P(NE)\<rfloor>\<^sup>c\<^sup>w"

 axiomatization where ref: "x r x" 
 axiomatization where sym: "x r y \<longrightarrow> y r x" 
 axiomatization where trans: "x r y \<and> y r z \<longrightarrow> x r z" 



(* T3: Necessarily, God exists *)
 theorem T3: "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. G(x))\<rfloor>\<^sup>c\<^sup>w" 
  proof -
   have L1: "\<lfloor>\<^bold>\<box>((\<^bold>\<exists>x. G(x)) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<exists>x. G(x))))\<rfloor>\<^sup>c\<^sup>w" 
proof -
  { fix ii :: i and mm :: \<mu> and iia :: i
    obtain bb :: "\<mu> \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> i \<Rightarrow> bool" where
      ff1: "(\<forall>m. (\<lfloor>(\<lambda>i. (\<^sup>\<not>G) m i \<or> (\<forall>p. (\<^bold>\<not>P p \<^bold>\<or> p m) i))\<rfloor>)) \<and> (\<forall>m. (\<lfloor>(\<lambda>i. (P (bb m i) \<^bold>\<and> (\<^sup>\<not>bb m i) m \<^bold>\<or> G m) i)\<rfloor>))"
      using G_def by moura
    have ff2: "(\<forall>p m. (\<lfloor>(\<lambda>i. (\<^sup>\<not>op ess p) m i \<or> p m i \<and> (\<forall>pa. (\<^sup>\<not>pa) m i \<or> (\<lfloor>(\<lambda>ia. (\<^bold>\<not>op r i) ia \<or> (\<forall>m. ((\<^sup>\<not>p) m \<^bold>\<or> pa m) ia))\<rfloor>)))\<rfloor>)) \<and> (\<forall>p m. (\<lfloor>(\<lambda>i. ((\<^sup>\<not>p) m i \<or> (\<exists>pa. (pa m \<^bold>\<and> \<^bold>\<diamond> (\<lambda>i. \<exists>m. (p m \<^bold>\<and> (\<^sup>\<not>pa) m) i)) i)) \<or> (p ess m) i)\<rfloor>))"
      by (metis ess_def) (* > 1.0 s, timed out *)
    { assume "cw r ii"
      have "(\<exists>p. ((\<^sup>\<not>p) mm \<^bold>\<and> P p) ii) \<or> (\<^bold>\<not>op r cw) ii \<or> (\<^sup>\<not>G) mm ii \<or> (\<^bold>\<not>op r ii \<^bold>\<or> mexiB G) iia"
        using ff2 ff1 by (metis (full_types) A1b A4 A5 NE_def trans)
      then have "(\<^bold>\<not>op r cw) ii \<or> (\<^sup>\<not>G) mm ii \<or> (\<^bold>\<not>op r ii \<^bold>\<or> mexiB G) iia"
        using ff1 by blast }
    then have "(\<^bold>\<not>op r cw) ii \<or> (\<^sup>\<not>G) mm ii \<or> (\<^bold>\<not>op r ii \<^bold>\<or> mexiB G) iia"
      by blast }
  then show ?thesis
    by blast
qed
    (* by (metis A1b A4 A5 G_def NE_def trans ess_def) *)
   hence "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G(x))\<rfloor>\<^sup>c\<^sup>w \<Longrightarrow> \<lfloor>\<^bold>\<diamond>(\<^bold>\<box>(\<^bold>\<exists>x. G(x)))\<rfloor>\<^sup>c\<^sup>w" by blast
   hence "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G(x))\<rfloor>\<^sup>c\<^sup>w \<Longrightarrow> \<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. G(x))\<rfloor>\<^sup>c\<^sup>w" by (metis C sym trans)
   thus "\<lfloor>\<^bold>\<box>(\<^bold>\<exists>x. G(x))\<rfloor>\<^sup>c\<^sup>w" using C by blast
  qed


(* Nitpick finds a model *)
 lemma True nitpick [satisfy, user_axioms] oops  


lemma MC_pre: "\<lfloor>\<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)\<rfloor>\<^sup>c\<^sup>w"  
  proof-
   have L1: "\<lfloor>\<^bold>\<forall>z. G(z) \<^bold>\<rightarrow> (\<^bold>\<forall>\<psi>. (\<psi>(z) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>x. G(x) \<^bold>\<rightarrow> \<psi>(x))))\<rfloor>\<^sup>c\<^sup>w" by (smt T2 ess_def)
   hence L2: "\<lfloor>\<^bold>\<forall>z. G(z) \<^bold>\<rightarrow> (\<Phi> \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>z. G(z) \<^bold>\<rightarrow> \<Phi>))\<rfloor>\<^sup>c\<^sup>w" by meson
   thus ?thesis using T3 ref by auto
  qed

lemma MC: "\<lfloor>\<^bold>\<forall>\<Phi>. \<Phi> \<^bold>\<rightarrow> (\<^bold>\<box> \<Phi>)\<rfloor>\<^sup>c\<^sup>w" using MC_pre by blast

end