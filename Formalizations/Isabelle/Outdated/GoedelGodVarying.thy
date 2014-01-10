(* Formalization of Goedel's ontological argument in Isabelle/HOL *)
(* Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo *)

(*
We present a formalization and (partial) automation of Dana Scott's version
of Goedel's ontological argument in quantified modal logic KB (QML KB). 
QML KB is in turn modeled as a fragment of Church's simple type theory (HOL). 
Thus, the formalization is essentially a formalization in HOL. 

The employed embedding of QML KB in HOL is adapting the ideas as presented in 
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
Note that our QML KB formalization employs quantification over individuals and 
quantification over sets of individuals (poperties).

Some further notes:
a) The Isabelle/HOL formalization closely follows the THF formalization available at: 
   https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations/THF
   This THF formalization has been the first successful attempt to formalize and 
   automate Goedel's ontological (July 2013). 
   Note that both LEO-II and Satallax can effectively automate the four steps in 
   the THF formalization. 
b) The Isabelle/HOL formalization is also closely related to the Coq formalization at:  
   https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations/Coq
   The interactive Coq formalization was produced shortly after the THF formalization.
c) In the Isabelle/HOL formalization all steps in the argument have been automated with
   sledgehammer performing remote calls to Satallax and LEO-II. These calls then 
   suggested respective metis calls as given below. 
d) The reconstruction with metis still fails for thm1, but when some further
   lemmata are introduced we get success; the respective lemmata are called help1-4.

Acknowledments: Nik Sultana, Jasmin Blanchette and Larry Paulson provided very important 
help wrt consistency checking in Isabelle (in an intermediate version of the Isabelle 
formalization axiom A2 got messed up; this was then detected by sledgehammer and 
nitpick and has subsequently been corrected again. As a result of this experience several
consistency checks with Nitpick have now been added to this file.
*)

theory GoedelGodVarying
imports Main HOL

begin
typedecl i  (* the type for possible worlds *)
typedecl mu (* the type for indiviuals      *)
(* r is an accessibility relation *)
consts r :: "i => i => bool" (infixr "r" 70) 
(* We don't restrict r at this point; in the first part (up to T2) 
   of the proof we thus work with modal logic K; later we will 
   require symmetry of r; but this only needed for T3 *)

(* classical negation lifted to possible worlds *)
definition mnot :: "(i => bool) => (i => bool)" ("m\<not>") where
  "m\<not> p = (\<lambda>w. \<not> p w)"
(* classical conjunction lifted to possible worlds *)
definition mand :: "(i => bool) => (i => bool) => (i => bool)" (infixr "m\<and>" 74) where
  "p m\<and> q = (\<lambda>w. p w \<and> q w)"
(* classical implication lifted to possible worlds *)
definition mimplies :: "(i => bool) => (i => bool) => (i => bool)" (infixr "m\<Rightarrow>" 79) where
  "p m\<Rightarrow> q = (\<lambda>w. p w \<longrightarrow> q w)"
(* universial quantification over individuals lifted to possible worlds *)
(* here we introduce varying individual domains *)
(* constant eiw stands for exists-in-world *)
consts eiw :: "i => mu => bool"  
(* we require the the domains characterised by eiw are all nonempty *)
axiomatization where
  nonempty: "\<forall>w. \<exists>x. eiw w x"
(* now the universal quantifier can be formalized based on eiw *)
definition mforall_ind :: "(mu => (i => bool)) => (i => bool)" ("\<forall>i") where
  "\<forall>i P = (\<lambda>w. \<forall>x. eiw w x \<longrightarrow> P x w)"
(* varying domain existential quantification is treated in a similar way *)
definition mexists_ind :: "(mu => (i => bool)) => (i => bool)" ("\<exists>i") where
  "\<exists>i P = (\<lambda>w. \<exists>x. eiw w x \<and> P x w)"
(* universial quantification over sets of individuals lifted to possible worlds *)
(* this remains constant domain *)
definition mforall_indset :: "((mu => (i => bool)) => (i => bool)) => (i => bool)" ("\<forall>p") where
  "\<forall>p P = (\<lambda>w. \<forall>x. P x w)"
(* the box operator based on r *)
definition mbox :: "(i => bool) => (i => bool)" ("\<box>") where
  "\<box> p = (\<lambda>w. \<forall>v. \<not> w r v \<or> p v)"
(* the diamond operator based on r *)
definition mdia :: "(i => bool) => (i => bool)" ("\<diamond>") where
  "\<diamond> p = (\<lambda>w. \<exists>v. w r v \<and> p v)" 
(* grounding of lifted modal formulas *)
definition valid :: "(i => bool) => bool" ("v") where
  "v p \<equiv> \<forall>w. p w"
 
(* Checking the consistency of the embedding with Nitpick *)
lemma True
   nitpick [satisfy, user_axioms, expect = genuine] 
   oops (* needed to continue *) 
  
(* Constant symbol for Goedel's positive *)
consts P :: "(mu => (i => bool)) => (i => bool)"
  
axiomatization where
  (* A1: Either the property or its negation are positive, but not both. *)
  A1a: "v (\<forall>p (\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<Rightarrow> m\<not> (P \<Phi>)))" and
  A1b: "v (\<forall>p (\<lambda>\<Phi>. m\<not> (P \<Phi>) m\<Rightarrow> P (\<lambda>x. m\<not> (\<Phi> x))))" and
  (* A2: A property necessarily implied by a positive property is positive. *)
  A2: "v (\<forall>p (\<lambda>\<Phi>. \<forall>p (\<lambda>\<psi>. (P \<Phi> m\<and> \<box> (\<forall>i (\<lambda>X. \<Phi> X m\<Rightarrow> \<psi> X))) m\<Rightarrow> P \<psi>)))"

(* Checking the consistency of assumptions up to here with Nitpick *)
lemma True
   nitpick [satisfy, user_axioms, expect = genuine] 
   oops (* needed to continue *) 

(* T1: Positive properties are possibly exemplified. *)
theorem T1: "v (\<forall>p (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<diamond> (\<exists>i \<Phi>)))"
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [provers = remote_leo2 remote_satallax] *)  
  using A2 A1a 
  unfolding mand_def mbox_def mdia_def mexists_ind_def 
            mforall_ind_def mforall_indset_def mimplies_def 
            mnot_def valid_def
  by metis

(* A God-like being possesses all positive properties. *)
definition G :: "mu => (i => bool)" where
  "G = (\<lambda>x. \<forall>p (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<Phi> x))"

(* A3: The property of being God-like is positive. *)
axiomatization where
  A3: "v (P G)"

(* Checking the consistency of assumptions up to here with Nitpick *)
lemma True
   nitpick [satisfy, user_axioms, expect = genuine] 
   oops (* needed to continue *) 

(* C: Possibly, God exists. *)
corollary C: "v (\<diamond> (\<exists>i G))" 
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [provers = remote_leo2 remote_satallax] *)  
  using A3 T1 
  unfolding mforall_indset_def mimplies_def valid_def
  by metis

(* A4: Positive properties are necessarily positive. *)
axiomatization where
  A4: "v (\<forall>p (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<box> (P \<Phi>)))"

(* An essence of an individual is a property possessed by it and necessarily 
   implying any of its properties. *)
definition ess :: "(mu => (i => bool)) => mu => (i => bool)" (infixr "ess" 85) where
  "p ess x = p x m\<and> \<forall>p (\<lambda>\<psi>. \<psi> x m\<Rightarrow> \<box> (\<forall>i (\<lambda>y. p y m\<Rightarrow> \<psi> y)))"

(* Checking the consistency of assumptions up to here with Nitpick *)
lemma True
   nitpick [satisfy, user_axioms, expect = genuine] 
   oops (* needed to continue *) 

(* T2: Being God-like is an essence of any God-like being. *)
theorem T2: "v (\<forall>i (\<lambda>x. G x m\<Rightarrow> G ess x))"
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [provers = remote_leo2 remote_satallax] *)  
  using A1a A1b A4
  unfolding valid_def mforall_indset_def mforall_ind_def mexists_ind_def 
            mnot_def mand_def mimplies_def mdia_def mbox_def G_def 
            ess_def 
  by metis

(* Necessary existence of an individual is the necessary exemplification 
   of all its essences. *)
definition NE :: "mu => (i => bool)" where
  "NE = (\<lambda>x. \<forall>p (\<lambda>\<Phi>. \<Phi> ess x m\<Rightarrow> \<box> (\<exists>i \<Phi>)))"

(* A5: Necessary existence is a positive property. *)
axiomatization where
  A5: "v (P NE)"
  
(* Additionally, r is now required symmetric, thus we work from now on in 
   modal logic KB instead of K *)
axiomatization where sym: "x r y \<longrightarrow> y r x"    
  
(* Checking the consistency of assumptions up to here with Nitpick *)
lemma True
   nitpick [satisfy, user_axioms, expect = genuine] 
   oops (* needed to continue *) 

(* We now introduce some help lemmata that are useful for proving thm1 with metis *)
(* With sledgehammer thm1 can be proved directly; but proof reconstruction with 
   metis still fails. To see this just try the following:

  theorem thm1: "v (\<box>(\<exists>i G))"
    using C T2 A5 sym
    unfolding valid_def mforall_indset_def mforall_ind_def mexists_ind_def mnot_def 
              mand_def mimplies_def mdia_def mbox_def G_def ess_def NE_def 
    sledgehammer [timeout = 60, provers = remote_leo2 remote_satallax] 
      
  This call is successful and suggests to use metis for reconstruction; but this metis 
  call still fails.  
*)
 
lemma help1: "v (\<diamond> (\<box> p)) \<Longrightarrow> v (\<box> p)"
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [provers = remote_leo2 remote_satallax] *)  
  using sym
  unfolding valid_def mdia_def mbox_def mimplies_def
  by metis

lemma help2: "v (\<diamond> p) \<and> v (p m\<Rightarrow> \<box> p) \<Longrightarrow> v (\<diamond> (\<box> p))"
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [provers = remote_leo2 remote_satallax] *)  
  unfolding valid_def mdia_def mbox_def mimplies_def      
  by metis
  
(* help3 is only required to prove help4 *)  
lemma help3: "v (\<forall>i (\<lambda>x. (G x m\<Rightarrow> G ess x m\<Rightarrow> \<box> (\<exists>i G))))"
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [timeout = 120, provers = remote_leo2 remote_satallax] *)
  using A5
  unfolding G_def NE_def mforall_ind_def mforall_indset_def mimplies_def valid_def
  by (metis (lifting, mono_tags))

lemma help4: "v (\<exists>i G m\<Rightarrow> \<box> (\<exists>i G))"
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [provers = remote_leo2 remote_satallax] *)
  using help3 T2 
  unfolding mexists_ind_def mforall_ind_def mimplies_def valid_def
  by (metis (lifting, mono_tags))

(* Checking the consistency of assumptions up to here with Nitpick *)
lemma True
   nitpick [satisfy, user_axioms, expect = genuine] 
   oops (* needed to continue *) 

(* thm1: Necessarily, God exists. *)
theorem T3: "v (\<box> (\<exists>i G))"
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [provers = remote_leo2 remote_satallax] *)
  using help1 help2 C help4
  by metis
  
(* to obtain the corollary below we additionally need reflexivity; 
   thus we move from logic KB to MB *)
axiomatization where refl: "x r x" 
  
(* Checking the consistency of assumptions up to here with Nitpick *)
lemma True
   nitpick [satisfy, user_axioms, expect = genuine] 
   oops (* needed to continue *) 

(* Corollary: God exists. *)
theorem cor: "v (\<exists>i G)"
  (* immeadiate success with sledgehammer *)
  (* sledgehammer [provers = remote_leo2 remote_satallax] *)
  using T3 refl
  unfolding valid_def mbox_def
  by metis

lemma MC: "v (p m\<Rightarrow> (\<box> p))"  
  -- {* sledgehammer [provers = remote\_satallax] *}
  -- {* by (metis T2 T3 ess\_def) *}
  nitpick

