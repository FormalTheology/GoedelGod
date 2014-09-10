(*<*) 
theory GoedelGodDivine
imports Main 

begin
(*>*)

text {* \newpage *}

section {* What does G\"odel mean with 'Positive' properties? And what not? *}
 text {* In order to better illustrate G\"odel's notion of 'Positive' properties, we reformulate the
entire theory and use 'Divine' instead of 'Positive'. Then we introduce orthogonal predicates 
'positive' and 'negative' and we show that God-like beings may well have 'positive' and 
'negative' properties as long as all these properties are divine properties.*}

text {* The types @{text "i"} for possible worlds. *}

  typedecl i    -- "the type for possible worlds" 
  typedecl \<mu>    -- "the type for indiviuals"      

text {* Accessibility relation @{text "r"}.*} 

  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"

text {* The @{text "B"} axiom (symmetry). *}

  axiomatization where sym: "x r y \<longrightarrow> y r x"    

text {* QML formulas are identified with certain HOL terms of type @{typ "i \<Rightarrow> bool"}. *}

  type_synonym \<sigma> = "(i \<Rightarrow> bool)"
 
text {* The classical connectives $\neg, \wedge, \rightarrow$, and $\forall$
(over individuals and over sets of individuals) and $\exists$ (over individuals) are
lifted to type $\sigma$. *}

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 79) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<Rightarrow>" 74) where "\<phi> m\<Rightarrow> \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 78) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"
  abbreviation mequiv :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 77) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>w. (\<phi> w \<longrightarrow> \<psi> w) \<and> (\<psi> w \<longrightarrow> \<phi> w))"   
  abbreviation mforall_ind :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
  abbreviation mforall_indset :: "((\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<Pi>") where "\<Pi> P \<equiv> (\<lambda>w. \<forall>x. P x w)"
  abbreviation mexists_ind :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>w. \<forall>v. \<not> w r v \<or> \<phi> v)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>w. \<exists>v. w r v \<and> \<phi> v)" 
  
text {* The meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>w. p w"
  
text {* Constant symbol @{text "Divine"} (G\"odel's `Positive') is declared. *}

  consts Divine :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

text {* The meaning of @{text "Divine"} is restricted by axioms @{text "A1(a/b)"}: $\all \phi 
[Divine(\neg \phi) \biimp \neg Divine(\phi)]$ (Either a property or its negation is divine, but not both.) 
and @{text "A2"}: $\all \phi \all \psi [(Divine(\phi) \wedge \nec \all x [\phi(x) \imp \psi(x)]) 
\imp Divine(\psi)]$ (A property necessarily implied by a divine property is divine). *}

  axiomatization where
    A1a: "[\<Pi> (\<lambda>\<Phi>. Divine (\<lambda>x. m\<not> (\<Phi> x)) m\<Rightarrow> m\<not> (Divine \<Phi>))]" and
    A1b: "[\<Pi> (\<lambda>\<Phi>. m\<not> (Divine \<Phi>) m\<Rightarrow> Divine (\<lambda>x. m\<not> (\<Phi> x)))]" and
    A2:  "[\<Pi> (\<lambda>\<Phi>. \<Pi> (\<lambda>\<psi>. (Divine \<Phi> m\<and> \<box> (\<forall> (\<lambda>x. \<Phi> x m\<Rightarrow> \<psi> x))) m\<Rightarrow> Divine \<psi>))]"

text {* We prove theorem T1: $\all \varphi [Divine(\varphi) \imp \pos \ex x \varphi(x)]$ (Divine 
properties are possibly exemplified). T1 is proved directly by Sledghammer with command @{text 
"sledgehammer [provers = remote_leo2]"}. This successful attempt then suggests to 
instead try the Metis call in the line below. This Metis call generates a proof object 
that is verified in Isabelle/HOL's kernel. *}
 
  theorem T1: "[\<Pi> (\<lambda>\<Phi>. Divine \<Phi> m\<Rightarrow> \<diamond> (\<exists> \<Phi>))]"  
  sledgehammer [provers = remote_leo2] 
  by (metis A1a A2)

text {* Next, the symbol @{text "G"} for `God-like'  is introduced and defined 
as $G(x) \biimp \forall \phi [Divine(\phi) \to \phi(x)]$ (A God-like being possesses 
all divine properties). *} 

  definition G :: "\<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>x. \<Pi> (\<lambda>\<Phi>. Divine \<Phi> m\<Rightarrow> \<Phi> x))"   

text {* Axiom @{text "A3"} is added: $Divine(G)$ (The property of being God-like is divine).
Sledgehammer and Metis then prove corollary @{text "C"}: $\pos \ex x G(x)$ 
(Possibly, God exists). *} 
 
  axiomatization where A3:  "[Divine G]" 

  corollary C: "[\<diamond> (\<exists> G)]" 
  sledgehammer [provers = remote_leo2] by (metis A3 T1)

text {* Axiom @{text "A4"} is added: $\all \phi [Divine(\phi) \to \Box \; Divine(\phi)]$ 
(Divine properties are necessarily divine). *}

  axiomatization where A4:  "[\<Pi> (\<lambda>\<Phi>. Divine \<Phi> m\<Rightarrow> \<box> (Divine \<Phi>))]" 

text {* Symbol @{text "ess"} for `Essence' is introduced and defined as 
$\ess{\phi}{x} \biimp \phi(x) \wedge \all \psi (\psi(x) \imp \nec \all y (\phi(y) 
\imp \psi(y)))$ (An \emph{essence} of an individual is a property possessed by it 
and necessarily implying any of its properties). *}

  definition ess :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "ess" 85) where
    "\<Phi> ess x = \<Phi> x m\<and> \<Pi> (\<lambda>\<psi>. \<psi> x m\<Rightarrow> \<box> (\<forall> (\<lambda>y. \<Phi> y m\<Rightarrow> \<psi> y)))"

text {* Next, Sledgehammer and Metis prove theorem @{text "T2"}: $\all x [G(x) \imp \ess{G}{x}]$ 
(Being God-like is an essence of any God-like being). *}

  theorem T2: "[\<forall> (\<lambda>x. G x m\<Rightarrow> G ess x)]"
  sledgehammer [provers = remote_leo2] by (metis A1b A4 G_def ess_def)

text {* Symbol @{text "NE"}, for `Necessary Existence', is introduced and
defined as $\NE(x) \biimp \all \phi [\ess{\phi}{x} \imp \nec \ex y \phi(y)]$ (Necessary 
existence of an individual is the necessary exemplification of all its essences). *}

  definition NE :: "\<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>x. \<Pi> (\<lambda>\<Phi>. \<Phi> ess x m\<Rightarrow> \<box> (\<exists> \<Phi>)))"

text {* Moreover, axiom @{text "A5"} is added: $Divine(\NE)$ (Necessary existence is a divine 
property). *}

  axiomatization where A5:  "[Divine NE]"

text {* Finally, Sledgehammer and Metis prove the main theorem @{text "T3"}: $\nec \ex x G(x)$ 
(Necessarily, God exists). *}

  theorem T3: "[\<box> (\<exists> G)]" 
  sledgehammer [provers = remote_leo2] by (metis A5 C T2 sym G_def NE_def)

  corollary C2: "[\<exists> G]" 
  sledgehammer [provers = remote_leo2](T1 T3 G_def sym) by (metis T1 T3 G_def sym)

text {* The consistency of the entire theory is checked with Nitpick. *}

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops 
    
text {* It has been critisized that G\"odel's ontological argument implies what is called the 
modal collapse. The prover Satallax \cite{Satallax} can indeed show this, but verification with 
Metis still fails. *} 
  
  lemma MC: "[p m\<Rightarrow> (\<box> p)]"
  using T2 T3 ess_def sym sledgehammer [provers = remote_satallax] oops

text {* We now introduce some orthogonal predicates 'positive' and 'negative'. *}

  consts positive :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" 
  consts negative :: "(\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" 

  axiomatization where
    axTest1  : "[positive(\<phi>) m\<or> negative(\<phi>)]" and
    axTest2 : "[positive(\<phi>) m\<equiv> m\<not> (negative(\<phi>))]" and
    axTest3  : "[m\<not> (positive(\<phi>)) m\<equiv> (positive (\<lambda>x . m\<not> (\<phi> x)))]" and
    axTest4  : "[m\<not> (negative(\<phi>)) m\<equiv> (negative (\<lambda>x . m\<not> (\<phi> x)))]"     

text {* We model a concrete God-like being called @{text "god1"}. @{text "god1"} is omniscient, 
punitive, and a fan of the Bayern Munich soccer team. Omniscience is modeled as a positive property 
and the other two properties are declared as negative. *}

  consts god1 :: "\<mu>"
  consts omniscient :: "\<mu> \<Rightarrow> \<sigma>"
  consts fanOfBayernMunich :: "\<mu> \<Rightarrow> \<sigma>"
  consts punitive :: "\<mu> \<Rightarrow> \<sigma>"
  
  axiomatization where
    axTest5 : "[positive(omniscient) m\<and> negative(punitive) m\<and> negative(fanOfBayernMunich)]" and
    axTest6 : "[omniscient(god1) m\<and> punitive(god1) m\<and> fanOfBayernMunich(god1)]" and
    axTest7 : "[G god1]"

text {* Nitpick confirms that these assumptions are consistent.  *}

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops 

text {* We prove that the properties of @{text "god1"} are all divine properties. *}

  lemma DivineProps : "[Divine(omniscient) m\<and> Divine(punitive) m\<and> Divine(fanOfBayernMunich)]"
  sledgehammer [provers = remote_satallax]
  by (metis A1b G_def axTest6 axTest7)

text {* \newpage *}

(*<*) 
end
(*>*) 