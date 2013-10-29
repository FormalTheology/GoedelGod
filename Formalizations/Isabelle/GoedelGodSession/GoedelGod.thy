(*<*) 
theory GoedelGod
imports Main

begin
(*>*)

section {* Introduction *}
 text {* A formalization and (partial) automation of Dana Scott's version \cite{ScottNotes}
 of Goedel's ontological argument \cite{GoedelNotes} in quantified modal logic KB (QML KB) is presented. 
 QML KB is in turn modeled as a fragment of classical higher-order logic (HOL). 
 Thus, the formalization is essentially a formalization in HOL. The employed embedding 
 of QML KB in HOL is adapting the work of Benzm\"uller and Paulson \cite{J23,B9}.
 Note that our QML KB formalization employs quantification over individuals and 
 quantification over sets of individuals (poperties).

 The formalization presented here has carried and formally verified in the Isabelle/HOL 
 proof assistant; for more information on this system we refer to the textbook by Nipkow, 
 Paulson, and Wenzel \cite{Isabelle}. More recent tutorials on Isabelle can be found 
 at \url{http://isabelle.in.tum.de}.

 Some further notes:
 \begin{enumerate}
 \item This LaTeX text document has been produced automatically from the Isabelle source
 code document at \url{??? todo ???} with the Isabelle build tool.
 \item The formalization presented here follows the THF \cite{J22} formalization available at: 
    \url{https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations/THF}
 \item The formalization is also related to the Coq \cite{Coq} formalization at:  
    \url{https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations/Coq}
 \item All reasoning gaps in Scott's proof script have been automated 
    with Sledgehammer \cite{Sledgehammer} performing remote calls to Satallax 
    \cite{Satallax} and LEO-II \cite{LEO-II}. These calls then suggested respective 
    Metis \cite{Metis} calls as given below. Metis proofs are verified in Isabelle/HOL.
 \item The reconstruction with Metis still fails for Theorem T3, but when some further
    lemmata are introduced we get success; these lemmata are called help1-4.
 \item For consistency checking the Nitpick model finder \cite{Nitpick} has been employed.
 \end{enumerate} *}

section {* An Embedding of QML KB in HOL *}

text {* Types for possible worlds and for individuals. *}

  typedecl i     -- "the type for possible worlds" 
  typedecl mu    -- "the type for indiviuals"      

text {* An accessibility relation on worlds.*} 

  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"

 text {* The B axiom (symmetry) for relation r; B is only needed for proving theorem T3. *}

  axiomatization where sym: "x r y \<longrightarrow> y r x"    

 text {* QML formulas are identified with certain HOL terms of type @{typ "i \<Rightarrow> bool"}. 
 This type will be abbreviated in the remainder as @{text "\<sigma>"} *}

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"
 
 text {* The classical connectives $\neg, \wedge, \Rightarrow$, and $\forall$
 (for individuals and over sets of individuals) and $\exists$ (over individuals) are
 lifted to type $\sigma$. Further connectives could be introduced analogously. *}

  definition mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> p = (\<lambda>w. \<not> p w)"    
  definition mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 74) where "p m\<and> q = (\<lambda>w. p w \<and> q w)"   
  definition mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<Rightarrow>" 79) where "p m\<Rightarrow> q = (\<lambda>w. p w \<longrightarrow> q w)"  
  definition mforall_ind :: "(mu \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>i") where "\<forall>i P = (\<lambda>w. \<forall>x. P x w)"   
  definition mexists_ind :: "(mu \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>i") where "\<exists>i P = (\<lambda>w. \<exists>x. P x w)"
  definition mforall_indset :: "((mu \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>p") where "\<forall>p P = (\<lambda>w. \<forall>x. P x w)"
  definition mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> p = (\<lambda>w. \<forall>v. \<not> w r v \<or> p v)"
  definition mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> p = (\<lambda>w. \<exists>v. w r v \<and> p v)" 

 text {* For the grounding of lifted formulas the meta-predicate @{text "valid"} is 
 introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  definition valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
 
 text {* The model finder Nitpick can now be used to confirm that the axioms and 
 definitions above are consistent. Unfortunately, the respective call-command for 
 Nitpick is not very intuitive. *}

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops 
  
section {* The Formalization of G\"odel's Definitions and Axioms *}

 text {* We introduce constant symbol @{text "P"} (G\"odel's "Positive"). *}

  consts P :: "(mu \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

 text {* The meaning of @{text "P"} is constrained by axioms 
 @{text "A1(a/b)"}: $\all \phi [P(\neg \phi) \biimp \neg P(\phi)]$ (Either a property or 
 its negation is positive, but not both) and 
 @{text "A2"}: $\all \phi \all \psi [(P(\phi) \wedge \nec \all x [\phi(x) \imp \psi(x)]) 
 \imp P(\psi)]$ (A property necessarily implied by a positive property is positive). *}

  axiomatization where
    A1a: "[\<forall>p (\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<Rightarrow> m\<not> (P \<Phi>))]" and
    A1b: "[\<forall>p (\<lambda>\<Phi>. m\<not> (P \<Phi>) m\<Rightarrow> P (\<lambda>x. m\<not> (\<Phi> x)))]" and
    A2:  "[\<forall>p (\<lambda>\<Phi>. \<forall>p (\<lambda>\<psi>. (P \<Phi> m\<and> \<box> (\<forall>i (\<lambda>X. \<Phi> X m\<Rightarrow> \<psi> X))) m\<Rightarrow> P \<psi>))]"

 text {* We prove theorem T1: $\all \varphi [P(\varphi) \imp \pos \ex x \varphi(x)]$ 
         (Positive properties are possibly exemplified).  
         T1 is proved directly by Sledghammer with command 
         @{text "sledgehammer [provers = remote_leo2 remote_satallax]"}. This successful 
         attempt then suggest to instead try the Metis call below.*}
 
  theorem T1: "[\<forall>p (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<diamond> (\<exists>i \<Phi>))]"  
    using A2 A1a unfolding mand_def mbox_def mdia_def mexists_ind_def mforall_ind_def 
                           mforall_indset_def mimplies_def mnot_def valid_def
    by metis

 text {* Next, we introduce the symbol @{text "G"}, G\"odel's "God-like", which is defined 
 as $G(x) \biimp \forall \phi [P(\phi) \to \phi(x)]$ (A God-like being possesses 
 all positive properties:). *} 

  definition G :: "mu \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<forall>p (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<Phi> x))"   

 text {* We add axiom @{text "A3"}: $P(G)$ (The property of being God-like is positive) 
 and prove corollary @{text "C"}: $\pos \ex x G(x)$ (Possibly, God exists). This
 this is directly proved by Sledgehammer, which then suggests the Metis call below.*} 
 
  axiomatization where A3:  "[P G]" 

  corollary C: "[\<diamond> (\<exists>i G)]" 
    using A3 T1 unfolding mforall_indset_def mimplies_def valid_def by metis

 text {* We add axiom @{text "A4"}: $\all \phi [P(\phi) \to \Box \; P(\phi)]$ 
 (Positive properties are necessarily positive). *}

  axiomatization where A4:  "[\<forall>p (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<box> (P \<Phi>))]" 

 text {* We introduce symbol @{text "ess"}, for "Essence", which is defined as 
 $\ess{\phi}{x} \biimp \phi(x) \wedge \all \psi (\psi(x) \imp \nec \all y (\phi(y) 
 \imp \psi(y)))$ (An \emph{essence} of an individual is a property possessed by it 
 and necessarily implying any of its properties). *}

  definition ess :: "(mu \<Rightarrow> \<sigma>) \<Rightarrow> mu \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x m\<and> \<forall>p (\<lambda>\<psi>. \<psi> x m\<Rightarrow> \<box> (\<forall>i (\<lambda>y. \<Phi> y m\<Rightarrow> \<psi> y)))"

 text {* We now prove theorem @{text "T2"}: $\all x [G(x) \imp \ess{G}{x}]$ (Being 
 God-like is an essence of any God-like being). Again, Sledgehammer is used first, 
 which then suggests the Metis call below. *}

  theorem T2: "[\<forall>i (\<lambda>x. G x m\<Rightarrow> G ess x)]"
    using A1a A1b A4 unfolding valid_def mforall_indset_def mforall_ind_def mexists_ind_def mnot_def
                                      mand_def mimplies_def mdia_def mbox_def G_def ess_def 
   by metis

 text {* Now, symbol @{text "NE"}, for "Necessary Existence", is introduced. It is 
 defined as $\NE(x) \biimp \all \phi [\ess{\phi}{x} \imp \nec \ex y \phi(y)]$ (Necessary 
 existence of an individual is the necessary exemplification of all its essences). *}

  definition NE :: "mu \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<forall>p (\<lambda>\<Phi>. \<Phi> ess x m\<Rightarrow> \<box> (\<exists>i \<Phi>)))"

 text {* We add axiom @{text "A5"}: $P(\NE)$ (Necessary existence is a positive property) *}

  axiomatization where A5:  "[P NE]"

 text {* The main theorem T3: $\nec \ex x G(x)$ (Necessarily, God exists) can be proven
 directly with Sledgehammer: 
 @{text "theorem T3: \"[\<box> (\<exists>i G)]\" sledgehammer [provers = remote_leo2 remote_satallax]"} 
 , but the suggested Metis call then unfortunately still fails. In order to 
 obtain a full verification of the proof we therefore introduce some further lemmata.*}

  lemma help1: "[\<diamond> (\<box> p)] \<Longrightarrow> [\<box> p]" 
    using sym unfolding valid_def mdia_def mbox_def by metis

  lemma help2: "[\<diamond> p] \<and> [p m\<Rightarrow> \<box> p] \<Longrightarrow> [\<diamond> (\<box> p)]" 
    unfolding valid_def mdia_def mbox_def mimplies_def by metis
  
  lemma help3: "\<forall>x. [G x m\<Rightarrow> G ess x m\<Rightarrow> \<box> (\<exists>i G)]"
    using A3 A5 unfolding G_def mforall_indset_def mimplies_def NE_def valid_def
    by (metis (lifting, mono_tags)) 

  lemma help4: "[\<exists>i G m\<Rightarrow> \<box> (\<exists>i G)]"
    using help3 T2 unfolding mexists_ind_def mforall_ind_def mimplies_def valid_def
    by metis

 text {* Now, also Metis succeeds with proving theorem @{text "T3"}, and we also get
 @{text "T4"}: *}

  theorem T3: "[\<box> (\<exists>i G)]" using help1 help2 C help4 by metis

 text {* Finally, we verify the consistency of our entire theory with Nitpick. *}

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops 

 text {*  \paragraph{Acknowledgments:} Nik Sultana, Jasmin Blanchette and Larry Paulson provided very important 
 help wrt consistency checking in Isabelle. Jasmin Blanchette also showed us how to produce latex documents from Isabelle files. 
 *}

(*<*) 
end
(*>*) 