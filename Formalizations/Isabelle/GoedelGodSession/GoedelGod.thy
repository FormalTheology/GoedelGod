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
 Note that the QML KB formalization employs quantification over individuals and 
 quantification over sets of individuals (poperties).

 The formalization presented here has been carried and formally verified in the Isabelle/HOL 
 proof assistant; for more information on this system see the textbook by Nipkow, 
 Paulson, and Wenzel \cite{Isabelle}. More recent tutorials on Isabelle can be found 
 at: \url{http://isabelle.in.tum.de}.
 

 Some further notes: \sloppy
 \begin{enumerate}
 \item This LaTeX text document has been produced automatically from the Isabelle source
 code document at 
 \url{https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations/Isabelle/GoedelGodSession} 
 with the Isabelle build tool.
 \item The formalization presented here is related to the THF \cite{J22} and 
    Coq \cite{Coq} formalizations at
    \url{https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations/}.
 \item All reasoning gaps in Scott's proof script have been automated 
    with Sledgehammer \cite{Sledgehammer}, performing remote calls to the higher-order automated
    theorem prover LEO-II \cite{LEO-II}. These calls suggest the 
    Metis \cite{Metis} calls as given below. The Metis proofs are verified in Isabelle/HOL.
 \item For consistency checking, the model finder \cite{Nitpick} has been employed.
 \end{enumerate} *}

section {* An Embedding of QML KB in HOL *}

text {* The types @{text "i"} for possible worlds (or states) and $\mu$ for individuals 
are introduced. *}

  typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for indiviuals"      

text {* Possible worlds are connected by an accessibility relation @{text "r"}.*} 

  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"

text {* The @{text "B"} axiom (symmetry) for relation r is stated. @{text "B"} is needed only 
for proving theorem T3. *}

  axiomatization where sym: "x r y \<longrightarrow> y r x"    

text {* QML formulas are identified with certain HOL terms of type @{typ "i \<Rightarrow> bool"}. 
This type will be abbreviated in the remainder as @{text "\<sigma>"}. *}

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"
 
text {* The classical connectives $\neg, \wedge, \rightarrow$, and $\forall$
(over individuals and over sets of individuals) and $\exists$ (over individuals) are
lifted to type $\sigma$. Further connectives could be introduced analogously. Definitions 
could be used instead of abbreviations. *}

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 79) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<Rightarrow>" 74) where "\<phi> m\<Rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
  abbreviation mforall_ind :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mexists_ind :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mforall_indset :: "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<Pi>") where "\<Pi> P \<equiv> (\<lambda>w. \<forall>x. P x w)"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v. \<not> w r v \<or> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 

text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  
section {* G\"odel's Ontological Argument *}  
  
text {* Constant symbol @{text "P"} (G\"odel's "Positive") is introduced. *}

  consts P :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

text {* The meaning of @{text "P"} is restricted by axioms @{text "A1(a/b)"}: $\all \phi 
[P(\neg \phi) \biimp \neg P(\phi)]$ (Either a property or its negation is positive, but not both.) 
and @{text "A2"}: $\all \phi \all \psi [(P(\phi) \wedge \nec \all x [\phi(x) \imp \psi(x)]) 
\imp P(\psi)]$ (A property necessarily implied by a positive property is positive). *}

  axiomatization where
    A1a: "[\<Pi> (\<lambda>\<Phi>. P (\<lambda>x. m\<not> (\<Phi> x)) m\<Rightarrow> m\<not> (P \<Phi>))]" and
    A1b: "[\<Pi> (\<lambda>\<Phi>. m\<not> (P \<Phi>) m\<Rightarrow> P (\<lambda>x. m\<not> (\<Phi> x)))]" and
    A2:  "[\<Pi> (\<lambda>\<Phi>. \<Pi> (\<lambda>\<psi>. (P \<Phi> m\<and> \<box> (\<forall> (\<lambda>x. \<Phi> x m\<Rightarrow> \<psi> x))) m\<Rightarrow> P \<psi>))]"

text {* We prove theorem T1: $\all \varphi [P(\varphi) \imp \pos \ex x \varphi(x)]$ (Positive 
properties are possibly exemplified). T1 is proved directly by Sledghammer with command @{text 
"sledgehammer [provers = remote_leo2]"}. This successful attempt then suggests to 
instead try the Metis call in the line below. This Metis call generates a proof object 
that is verified in Isabelle/HOL's kernel. *}
 
  theorem T1: "[\<Pi> (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<diamond> (\<exists> \<Phi>))]"  
  sledgehammer [provers = remote_leo2] 
  by (metis A1a A2)

text {* Next, the symbol @{text "G"} for "God-like" is introduced and defined 
as $G(x) \biimp \forall \phi [P(\phi) \to \phi(x)]$ (A God-like being possesses 
all positive properties:). *} 

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<Pi> (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<Phi> x))"   

text {* Axiom @{text "A3"} is added: $P(G)$ (The property of being God-like is positive).
Sledgehammer and Metis then prove corollary @{text "C"}: $\pos \ex x G(x)$ 
(Possibly, God exists). *} 
 
  axiomatization where A3:  "[P G]" 

  corollary C: "[\<diamond> (\<exists> G)]" 
  (* sledgehammer [provers = remote_leo2] *)
  using A3 T1 by metis

text {* Axiom @{text "A4"} is added: $\all \phi [P(\phi) \to \Box \; P(\phi)]$ 
(Positive properties are necessarily positive). *}

  axiomatization where A4:  "[\<Pi> (\<lambda>\<Phi>. P \<Phi> m\<Rightarrow> \<box> (P \<Phi>))]" 

text {* Symbol @{text "ess"} for "Essence" is introduced and defined as 
$\ess{\phi}{x} \biimp \phi(x) \wedge \all \psi (\psi(x) \imp \nec \all y (\phi(y) 
\imp \psi(y)))$ (An \emph{essence} of an individual is a property possessed by it 
and necessarily implying any of its properties.). *}

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x m\<and> \<Pi> (\<lambda>\<psi>. \<psi> x m\<Rightarrow> \<box> (\<forall> (\<lambda>y. \<Phi> y m\<Rightarrow> \<psi> y)))"

text {* Next, Sledgehammer and Metis prove theorem @{text "T2"}: $\all x [G(x) \imp \ess{G}{x}]$ 
(Being God-like is an essence of any God-like being). *}

  theorem T2: "[\<forall> (\<lambda>x. G x m\<Rightarrow> G ess x)]"
  sledgehammer [provers = remote_leo2]
  by (metis A1b A4 G_def ess_def)

text {* Symbol @{text "NE"}, for "Necessary Existence", is introduced and
defined as $\NE(x) \biimp \all \phi [\ess{\phi}{x} \imp \nec \ex y \phi(y)]$ (Necessary 
existence of an individual is the necessary exemplification of all its essences.). *}

  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<Pi> (\<lambda>\<Phi>. \<Phi> ess x m\<Rightarrow> \<box> (\<exists> \<Phi>)))"

text {* Moreover, axiom @{text "A5"} is added: $P(\NE)$ (Necessary existence is a positive 
property). *}

  axiomatization where A5:  "[P NE]"

text {* Finally, Sledgehammer and Metis prove the main theorem @{text "T3"}: $\nec \ex x G(x)$ 
(Necessarily, God exists). *}

  theorem T3: "[\<box> (\<exists> G)]" 
  sledgehammer [provers = remote_leo2]
  by (metis A5 C T2 sym G_def NE_def)

  corollary T4: "[\<exists> G]" 
  sledgehammer [provers = remote_leo2]
  by (metis T1 T3 G_def sym)

text {* The consistency of the entire theory is checked with Nitpick. *}

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops 
  
text {* We check for the modal collapse. Satallax can prove this. *} 
  
  lemma MC: "[p m\<Rightarrow> (\<box> p)]"
  using T2 T3 ess_def sledgehammer [provers = remote_satallax] oops
  
text {* \paragraph{Acknowledgments:} Nik Sultana, Jasmin Blanchette and Larry Paulson provided 
very important help wrt consistency checking in Isabelle. Jasmin Blanchette instructed us on how to 
produce latex documents from Isabelle sources, and he showed us useful tricks in Isabelle. *}

(*<*) 
end
(*>*) 