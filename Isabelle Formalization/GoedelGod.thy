(* Formalization of Goedel's ontological argument in Isabelle/HOL *)
(* Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo *)
(* Date: August 11, 2013; update on August 17, 2013 *)

(*
We present a formalization and (partial) automation of Goedel's
ontological argument in quantified modal logic S5 (QML S5). QML S5 is in 
turn modeled as a fragment of Church's simple type theory (HOL). Thus, the
formalization is essentially a formalization in HOL. 

The employed embedding of QML S5 in HOL is adapting the ideas as presented in 
-- Quantified Multimodal Logics in Simple Type Theory (Christoph Benzmueller, 
   Lawrence Paulson), In Logica Universalis (Special Issue on Multimodal 
   Logics), volume 7, number 1, pp. 7-20, 2013. 
and in 
-- Exploring Properties of Normal Multimodal Logics in Simple Type Theory 
   with LEO-II (Christoph Benzmueller, Lawrence Paulson), Chapter in Reasoning 
   in Simple Type Theory --- Festschrift in Honor of Peter B. Andrews on His 
   70th Birthday (Christoph Benzmueller, Chad Brown, Joerg Siekmann, Richard 
   Statman, eds.), College Publications, Studies in Logic, Mathematical Logic 
   and Foundations, pp. 386-406, 2008.
Note that our QML S5 formalization employs quantification over individuals and 
quantification over sets of individuals.

Some further notes:
a) The Isabelle/HOL formalization closely follows the THF formalization available at: 
   https://github.com/FormalTheology/GoedelGod/tree/master/TPTP%20THF%20Formalization
   This THF formalization has been the first successful attempt to formalize and 
   automate Goedel's ontological (July 2013). 
   Note that both LEO-II and Satallax can effectively automate the four steps in 
   the THF formalization. 
b) The Isabelle/HOL formalization is also closely related to the Coq formalization at:  
   https://github.com/FormalTheology/GoedelGod/blob/master/Coq%20Formalization/ExplicitModalSemanticEncoding/GoedelGod.v
   This interactive Coq formalization was produced shortly after the THF formalization.
c) In the Isabelle/HOL formalization all steps in the argument have been automated with
   sledgehammer performing remote calls to Satallax and LEO-II. These calls then 
   suggested respective metis calls as given below. 
d) The re-proof/reconstruction with metis still fails for thm1, but when some further
   lemmata are introduced we get success; the respective lemmata are called help1-4.
*)

theory GoedelGod
imports Main HOL

begin
typedecl i  (* the type for possible worlds *)
typedecl mu (* the type for indiviuals      *)

(* r is an accessibility relation *)
consts r :: "i => i => bool" (infixr "r" 70) 

(* r is reflexive, symmetric and transitive *)
axiomatization where 
  refl: "x r x" and
  sym: "x r y \<longrightarrow> y r x" and
  trans: "x r y & y r z \<longrightarrow> x r z"
  
(* classical negation lifted to possible worlds *)   
definition mnot :: "(i => bool) => (i => bool)" ("m\<not>") where
  "mnot p = (\<lambda>W. \<not> p W)"

(* classical conjunction lifted to possible worlds *)
definition mand :: "(i => bool) => (i => bool) => (i => bool)" (infixr "m\<and>" 74) where
  "mand p q = (\<lambda>W. p W & q W) "  

(* classical implication lifted to possible worlds *)
definition mimplies :: "(i => bool) => (i => bool) => (i => bool)" (infixr "m\<Rightarrow>" 79) where
  "mimplies p q = (\<lambda>W. p W \<longrightarrow> q W)"

(* universial quantification over individuals lifted to possible worlds *)
definition mforall_ind :: "(mu => (i => bool)) => (i => bool)" ("\<forall>i") where
  "mforall_ind abstrP = (\<lambda>W. \<forall> X.  abstrP X W)"  
  
(* existential quantification over individuals lifted to possible worlds *)
definition mexists_ind :: "(mu => (i => bool)) => (i => bool)" ("\<exists>i") where
  "mexists_ind abstrP = (\<lambda>W. \<exists> X.  abstrP X W)"    
  
(* universial quantification over sets of individuals lifted to possible worlds *)
definition mforall_indset :: "((mu => (i => bool)) => (i => bool)) => (i => bool)" ("\<forall>iset") where
  "mforall_indset abstrP = (\<lambda>W. \<forall> X.  abstrP X W)"

(* the s5 box operator based on r *)
definition mbox_s5 :: "(i => bool) => (i => bool)" ("\<box>") where
  "mbox_s5 p = (\<lambda>W. \<forall> V. \<not> W r V \<or> p V)"
  
(* the s5 diamond operator based on r *)
definition mdia_s5 :: "(i => bool) => (i => bool)" ("\<diamond>") where
  "mdia_s5 p = (\<lambda>W. \<exists> V. W r V \<and> p V)"  
  
(* grounding of lifted modal formulas *)
definition valid :: "(i => bool) => bool" ("v") where
  "valid p == (\<forall> W. p W)"    
  
(* constant positive *)
consts pos :: "(mu => (i => bool)) => (i => bool)"
  
axiomatization where
  (* a1: Any property strictly implied by a positive property is positive. *)
  a1: "v (\<forall>iset (\<lambda>P. \<forall>iset (\<lambda>Q. ((pos P) m\<and> \<box> (\<forall>i (\<lambda>X. P X m\<Rightarrow> Q X))) m\<Rightarrow> pos Q )))" and
  (* a2a: If a property is positive then its negation is not positive. *)
  a2a: "v (\<forall>iset (\<lambda>P. pos P m\<Rightarrow> m\<not> (pos (\<lambda>W. m\<not> (P W)))))" and
  (* a2b: A property is positive when its negation is not positive. *)
  a2b: "v (\<forall>iset (\<lambda>P. m\<not> (pos (\<lambda>W. m\<not> (P W))) m\<Rightarrow> pos P))"

(* l1: Positive properties are eventually exemplified. *)
lemma l1: "v (\<forall>iset (\<lambda>P. (pos P) m\<Rightarrow> \<diamond> (\<exists>i (\<lambda>X. P X))))"
  (* l1 can be proved from a1 and a2a.
     sledgehammer with leo2 and satallax does find the proof; just try:
       sledgehammer [provers = remote_leo2 remote_satallax] 
     This call then suggests the use of metis; see below. *)
  using a1 a2a 
  unfolding mand_def mbox_s5_def mdia_s5_def mexists_ind_def 
            mforall_ind_def mforall_indset_def mimplies_def 
            mnot_def valid_def
  by metis

(* Definition of God: 
   X is God if and only if X incorporates all positive properties. *)
definition god :: "mu => (i => bool)" where
  "god = (\<lambda>X. \<forall>iset (\<lambda>P. (pos P) m\<Rightarrow> (P X)))"

(* a3: The property of being God-like is positive. *)
axiomatization where
  a3: "v (pos god)"

(* l2: Eventually God exists. *)
lemma l2: "v (\<diamond> (\<exists>i (\<lambda>X. god X)))" 
  (* l2 can be proved from l1 and a3.
       sledgehammer succeeds; try this: 
       sledgehammer [provers = remote_leo2 remote_satallax] 
     Note that god_def is not even needed.
   *)
  using a3 l1 unfolding mforall_indset_def mimplies_def valid_def
  by metis

(* Definition of essential:
   Property P is essential for X (and essence of X) if and only if P is a 
   property of X and every property Q that X has is strictly implied by P. *)
definition essential :: "(mu => (i => bool)) => mu => (i => bool)" where
  "essential p x = ( p x m\<and> \<forall>iset (\<lambda>Q. Q x m\<Rightarrow> \<box> (\<forall>i (\<lambda>Y. p Y m\<Rightarrow> (Q Y)))))"

(* a4: Positive properties are necessary positive properties. *)
axiomatization where
  a4: "v (\<forall>iset (\<lambda>P. pos P m\<Rightarrow> (\<box> (pos P))))"

(* l3: If X is a God-like being, then the property of being God-like 
   is an essence of X. *)
lemma l3: "v (\<forall>i (\<lambda>X. god X m\<Rightarrow> (essential god X)))"
  using a2a a2b a4 sym
  unfolding valid_def mforall_indset_def mforall_ind_def mexists_ind_def 
            mnot_def mand_def mimplies_def mdia_s5_def mbox_s5_def god_def 
            essential_def 
  by metis

(* Definition of necessary existence:
   X necessarily exists if and only if every essence of X is necessarily 
   exemplified. *)
definition nec_exists :: "mu => (i => bool)" where
  "nec_exists = (\<lambda>X. (\<forall>iset (\<lambda>P. essential P X m\<Rightarrow> \<box> (\<exists>i (\<lambda>Y. P Y)))))"

(* a5: Necessary existence is positive. *)
axiomatization where
  a5: "v (pos nec_exists)"

(* We now introduce some help lemmata that are useful for proving thm1 with metis *)
(* With Sledgehammer thm1 can be proved directly; but proof reconstruction with 
   metis still fails. To see this just try the following:

  theorem thm1: "v (\<box> (\<exists>i god))"
    using l2 l3 a5 sym refl
    unfolding valid_def mforall_indset_def mforall_ind_def mexists_ind_def mnot_def mand_def mimplies_def mdia_s5_def mbox_s5_def god_def essential_def nec_exists_def 
    sledgehammer [timeout = 60, provers = remote_satallax] 
   
  This call is successful and suggests to use metis for reconstruction; but this metis 
  call still fails.  
*)
  
lemma help1: "v (\<diamond> (\<box> p)) \<Longrightarrow> v (\<box> p)"  
  using sym trans
  unfolding valid_def mdia_s5_def mbox_s5_def mimplies_def
  by metis

lemma help2: "   v (\<diamond> p) & v (p m\<Rightarrow>  \<box> p) \<Longrightarrow> v (\<diamond> (\<box> p))"  
  unfolding valid_def mdia_s5_def mbox_s5_def mimplies_def      
  by metis
  
(* help3 is only required to prove help4 *)  
lemma help3:  "\<forall> X. v ((god X) m\<Rightarrow>  ((essential god X) m\<Rightarrow> (\<box> (\<exists>i god))))"
  using a3 a5
  unfolding god_def mforall_indset_def mimplies_def nec_exists_def valid_def
  by (metis (lifting, mono_tags)) 

lemma help4: "v ((\<exists>i god) m\<Rightarrow>  \<box> (\<exists>i god))"
  using help3 l3 
  unfolding mexists_ind_def mforall_ind_def mimplies_def valid_def
  by metis

(* thm1: Necessarily God exists. *)
theorem t: "v (\<box> (\<exists>i god))"
  using help1 help2 l2 help4
  by metis

(* Corollary c: God exists. *)
theorem c: "v (\<exists>i god)"
  (* metis can easily prove this *)
  using t refl
  unfolding valid_def mbox_s5_def
  by metis
