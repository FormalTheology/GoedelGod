(*<*) 
theory GoedelGodIntensional2
imports Main 

begin
(*>*)

section {* Introduction *}

 text {* Dana Scott's version \cite{ScottNotes} (cf.~Fig.~1)
 of G\"odel's proof of God's existence \cite{GoedelNotes} is 
 formalized in quantified modal logic KB (QML KB) within the proof assistant Isabelle/HOL. 
 QML KB is  modeled as a fragment of classical higher-order logic (HOL); 
 thus, the formalization is essentially a formalization in HOL. The employed embedding 
 of QML KB in HOL is adapting the work of Benzm\"uller and Paulson \cite{J23,B9}.
 Note that the QML KB formalization employs quantification over individuals and 
 quantification over sets of individuals (properties).

 The gaps in Scott's proof have been automated 
 with Sledgehammer \cite{Sledgehammer}, performing remote calls to the higher-order automated
 theorem prover LEO-II \cite{LEO-II}. Sledgehammer suggests the 
 Metis \cite{Metis} calls, which result in proofs that are verified by Isabelle/HOL.
 For consistency checking, the model finder Nitpick \cite{Nitpick} has been employed.
 The successfull calls to Sledgehammer
 are deliberately kept as comments in the file for demonstration purposes
 (normally, they are automatically eliminated by Isabelle/HOL).
 
 Isabelle is described in the textbook by Nipkow, 
 Paulson, and Wenzel \cite{Isabelle} and in tutorials available 
 at: \url{http://isabelle.in.tum.de}.
 
\subsection{Related Work}

 The formalization presented here is related to the THF \cite{J22} and 
 Coq \cite{Coq} formalizations at 
 \url{https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations/}.
 
 An older ontological argument by Anselm was formalized in PVS by John Rushby \cite{rushby}.
*}

section {* An Embedding of QML KB in HOL *}

text {* The types @{text "i"} for possible worlds and $\mu$ for individuals are introduced. *}

  typedecl i    -- "the type for possible worlds" 
  typedecl mu    -- "the type for indiviuals"      

text {* Possible worlds are connected by an accessibility relation @{text "r"}.*} 

  consts r :: "i \<Rightarrow> i \<Rightarrow> bool" (infixr "r" 70)    -- "accessibility relation r"   

text {* QML formulas are here translated as HOL terms of type @{typ "i \<Rightarrow> i \<Rightarrow> bool"}. 
This type is abbreviated as @{text "\<sigma>"}. The idea is that the first argument stands
for the original actual world, i.e. the world the evaluation of a formula has started in.
The second argument is the dynamically changing world in which the formula is evaluated. *}

  type_synonym \<sigma> = "(i \<Rightarrow> i \<Rightarrow> bool)"
  type_synonym \<mu> = "(i \<Rightarrow> i \<Rightarrow> mu)"
  
 
text {* The classical connectives $\neg, \wedge, \rightarrow$, and $\forall$
(over individuals and over sets of individuals) and $\exists$ (over individuals) are
lifted to type $\sigma$. The lifted connectives are @{text "m\<not>"}, @{text "m\<and>"}, @{text "m\<rightarrow>"},
@{text "\<forall>"}, and @{text "\<exists>"} (the latter two are modeled as constant symbols). 
Other connectives can be introduced analogously. We exemplarily do this for @{text "m\<or>"} , 
@{text "m\<equiv>"}, and @{text "mL="} (Leibniz equality on individuals). Moreover, the modal 
operators @{text "\<box>"} and @{text "\<diamond>"}  are introduced. Definitions could be used instead of 
abbreviations. Note how the first world is memorized in the definition of @{text "\<box>"} 
and @{text "\<diamond>"}, while the second world is dynamically modified. *}

  abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" ("m\<not>") where "m\<not> \<phi> \<equiv> (\<lambda>v. \<lambda>w. \<not> \<phi> v w)"    
  abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<and>" 51) where "\<phi> m\<and> \<psi> \<equiv> (\<lambda>v. \<lambda>w. \<phi> v w \<and> \<psi> v w)"   
  abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<or>" 50) where "\<phi> m\<or> \<psi> \<equiv> (\<lambda>v. \<lambda>w. \<phi> v  w \<or> \<psi> v w)"   
  abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<rightarrow>" 49) where "\<phi> m\<rightarrow> \<psi> \<equiv> (\<lambda>v. \<lambda>w. \<phi> v w \<longrightarrow> \<psi> v w)"  
  abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (infixr "m\<equiv>" 48) where "\<phi> m\<equiv> \<psi> \<equiv> (\<lambda>v. \<lambda>w. \<phi> v w \<longleftrightarrow> \<psi> v w)"  
  abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<forall>") where "\<forall> \<Phi> \<equiv> (\<lambda>v. \<lambda>w. \<forall>x. \<Phi> x v w)"   
  abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" ("\<exists>") where "\<exists> \<Phi> \<equiv> (\<lambda>v. \<lambda>w. \<exists>x. \<Phi> x v w)"
  abbreviation mLeibeq :: "\<mu> \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" (infixr "mL=" 52) where "x mL= y \<equiv> \<forall>(\<lambda>\<phi>. (\<phi> x m\<rightarrow> \<phi> y))"
  abbreviation mbox :: "\<sigma> \<Rightarrow> \<sigma>" ("\<box>") where "\<box> \<phi> \<equiv> (\<lambda>v. \<lambda>w. \<forall>u.  w r u \<longrightarrow> \<phi> v u)"
  abbreviation mdia :: "\<sigma> \<Rightarrow> \<sigma>" ("\<diamond>") where "\<diamond> \<phi> \<equiv> (\<lambda>v. \<lambda>w. \<exists>u. w r u \<and> \<phi> v u)" 
  
text {* For grounding lifted formulas, the meta-predicate @{text "valid"} is introduced. *}

  (*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
  abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("[_]") where "[p] \<equiv> \<forall>v. \<forall>w. p v w"
  
section {* G\"odel's Ontological Argument *}  
  
text {* Constant symbol @{text "P"} (G\"odel's `Positive') is declared. *}

  consts P :: "i \<Rightarrow> i \<Rightarrow> (i \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>"  

text {* The meaning of @{text "P"} is restricted by axioms @{text "A1(a/b)"}: $\all \phi 
[P(\neg \phi) \biimp \neg P(\phi)]$ (Either a property or its negation is positive, but not both.) 
and @{text "A2"}: $\all \phi \all \psi [(P(\phi) \wedge \nec \all x [\phi(x) \imp \psi(x)]) 
\imp P(\psi)]$ (A property necessarily implied by a positive property is positive). *}

  axiomatization where
    A1a: " \<forall>v w. ((\<forall>(\<lambda>\<Phi>. P v w (\<lambda>m n. (\<lambda>x. m\<not> (\<Phi> m n x))) m\<rightarrow> m\<not> (P v w \<Phi>))) v w)"
  axiomatization where   
    A1b: "\<forall>v w. ((\<forall>(\<lambda>\<Phi>. m\<not> (P v w \<Phi>) m\<rightarrow> P v w (\<lambda>m n. (\<lambda>x. m\<not> (\<Phi> m n x))))) v w)" 
  axiomatization where    
    A2:  "\<forall>v w. ((\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>\<Psi>. (P v w \<Phi> m\<and> \<box> (\<forall>(\<lambda>x. \<Phi> v w x m\<rightarrow> \<Psi> v w x))) m\<rightarrow> P v w \<Psi>))) v w)"

text {* We prove theorem T1: $\all \phi [P(\phi) \imp \pos \ex x \phi(x)]$ (Positive 
properties are possibly exemplified). T1 is proved directly by Sledgehammer with command @{text 
"sledgehammer [provers = remote_leo2]"}. 
Sledgehammer suggests to call Metis with axioms A1a and A2. 
Metis sucesfully generates a proof object 
that is verified in Isabelle/HOL's kernel. *}
 
  theorem T1: "\<forall>v w. ((\<forall>(\<lambda>\<Phi>. P v w \<Phi> m\<rightarrow> \<diamond> (\<exists> (\<Phi> v w)))) v w)"  
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A1a A2)

text {* Next, the symbol @{text "G"} for `God-like'  is introduced and defined 
as $G(x) \biimp \forall \phi [P(\phi) \to \phi(x)]$ \\ (A God-like being possesses 
all positive properties). *} 

  definition G :: "i \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where "G = (\<lambda>v. \<lambda>w. \<lambda>x. \<forall>(\<lambda>\<Phi>. P v w \<Phi> m\<rightarrow> \<Phi> v w x))"   

text {* Axiom @{text "A3"} is added: $P(G)$ (The property of being God-like is positive).
Sledgehammer and Metis then prove corollary @{text "C"}: $\pos \ex x G(x)$ 
(Possibly, God exists). *} 
 
  axiomatization where A3:  "\<forall>v w. (((P v w) G) v w)" 

  corollary C: "\<forall>v w. ((\<diamond> (\<exists> (G v w))) v w)" 
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A3 T1)

text {* Axiom @{text "A4"} is added: $\all \phi [P(\phi) \to \Box \; P(\phi)]$ 
(Positive properties are necessarily positive). *}

  axiomatization where A4:  "\<forall>v w. ((\<forall>(\<lambda>\<Phi>. P v w \<Phi> m\<rightarrow> \<box> (P v w \<Phi>))) v w)" 

text {* Symbol @{text "ess"} for `Essence' is introduced and defined as 
$$\ess{\phi}{x} \biimp \phi(x) \wedge \all \psi (\psi(x) \imp \nec \all y (\phi(y) 
\imp \psi(y)))$$ (An \emph{essence} of an individual is a property possessed by it and necessarily 
implying any of its properties). *}

  definition ess :: "i \<Rightarrow> i \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>) \<Rightarrow> (\<mu> \<Rightarrow> \<sigma>)" where
    "ess = (\<lambda>v w \<Phi> x. (\<Phi> x) m\<and> \<forall>(\<lambda>\<Psi>. \<Psi> x m\<rightarrow> \<box> (\<forall>(\<lambda>y. \<Phi> y m\<rightarrow> \<Psi> y))))"

text {* Next, Sledgehammer and Metis prove theorem @{text "T2"}: $\all x [G(x) \imp \ess{G}{x}]$ \\
(Being God-like is an essence of any God-like being). *}

  theorem T2: "\<forall>v w. ((\<forall>(\<lambda>x. G v w x m\<rightarrow> ess v w (G v w) x)) v w)"
  -- {* sledgehammer [provers = remote\_leo2] *}
  -- {* metis is too weak: by (metis A1b A4 G_def ess_def) *}
  oops
  
  axiomatization where T2: "\<forall>v w. ((\<forall>(\<lambda>x. G v w x m\<rightarrow> ess v w (G v w) x)) v w)"

text {* Symbol @{text "NE"}, for `Necessary Existence', is introduced and
defined as $$\NE(x) \biimp \all \phi [\ess{\phi}{x} \imp \nec \ex y \phi(y)]$$ (Necessary 
existence of an individual is the necessary exemplification of all its essences). *}

  definition NE :: "i \<Rightarrow> i \<Rightarrow> \<mu> \<Rightarrow> \<sigma>" where "NE = (\<lambda>v w x. \<forall>(\<lambda>\<Phi>. ess v w (\<Phi> v w) x m\<rightarrow> \<box> (\<exists> (\<Phi> v w))))"

text {* Moreover, axiom @{text "A5"} is added: $P(\NE)$ (Necessary existence is a positive 
property). *}

  axiomatization where A5:  "\<forall>v w. ((P v w NE) v w)"

text {* The @{text "B"} axiom (symmetry) for relation r is stated. @{text "B"} is needed only 
for proving theorem T3 and for corollary C2. *}

  axiomatization where sym: "x r y \<longrightarrow> y r x" 

text {* Finally, Sledgehammer and Metis prove the main theorem @{text "T3"}: $\nec \ex x G(x)$ \\
(Necessarily, God exists). *}

  theorem T3: "\<forall>v w. ((\<box> (\<exists> (G v w))) v w)"
  unfolding G_def
  -- {* sledgehammer [provers = remote\_leo2] *}
  oops
  
text {* Surprisingly, the following corollary can be derived even without the @{text "T"} axiom 
(reflexivity). *}

  corollary C2: "\<forall>v w. ((\<exists> (G v w)) v w)" 
  -- {* sledgehammer [provers = remote\_leo2] *}
  oops
  
text {* The consistency of the entire theory is confirmed by Nitpick. *}

  lemma True nitpick [satisfy, user_axioms, expect = genuine] oops


section {* Additional Results on G\"odel's God. *}  

text {* G\"odel's God is flawless: (s)he does not have non-positive properties. *}

  theorem Flawlessness: "\<forall>v w. ((\<forall>(\<lambda>\<Phi>. \<forall>(\<lambda>x. (G v w x m\<rightarrow> (m\<not> (P v w \<Phi>) m\<rightarrow> m\<not> (\<Phi> v w x)))))) v w)"
  -- {* sledgehammer [provers = remote\_leo2] *}
  by (metis A1b G_def) 
  
text {* There is only one God: any two God-like beings are equal. *}   
  
  theorem Monotheism: "\<forall>v w. ((\<forall>(\<lambda>x.\<forall>(\<lambda>y. (G v w x m\<rightarrow> (G v w y m\<rightarrow> (x mL= y)))))) v w)"
  -- {* sledgehammer [provers = remote\_leo2] *}
  oops
  
section {* Modal Collapse *}  

text {* G\"odel's axioms have been criticized for entailing the so-called 
modal collapse. The prover Satallax \cite{Satallax} confirms this. 
However, sledgehammer is not able to determine which axioms, 
definitions and previous theorems are used by Satallax;
hence it suggests to call Metis using everything, but this (unsurprinsingly) fails.
Attempting to use `Sledegehammer min' to minimize Sledgehammer's suggestion does not work.
Calling Metis with @{text "T2"}, @{text "T3"} and @{text "ess_def"} also does not work. *} 

  lemma MC: "\<forall>v w. ((\<forall>(\<lambda>\<Phi>.(\<Phi> m\<rightarrow> (\<box> \<Phi>)))) v w)"  
  -- {* sledgehammer [provers = remote\_satallax] *}
  -- {* by (metis T2 T3 ess\_def) *}
  oops
(*<*) 
end
(*>*) 