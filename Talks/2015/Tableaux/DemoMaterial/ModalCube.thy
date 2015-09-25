(*<*) 
theory ModalCube
imports Main

begin
(*>*)

text {* \begin{abstract}
We present an automated verification of the well-known
modal logic cube in Isabelle/HOL, in which we prove the inclusion relations
between the cube's logics using automated reasoning tools.
Prior work addresses this problem but without restriction to the modal logic cube,
and using encodings in first-order logic in 
combination with first-order automated theorem provers.
In contrast, our solution is
more elegant, transparent and effective. It employs an
embedding of quantified modal logic in classical higher-order
logic. Automated reasoning tools, such as Sledgehammer with LEO-II,
Satallax and CVC4, Metis and Nitpick, are employed to achieve full automation.
Though successful, the experiments also motivate some technical improvements 
in the Isabelle/HOL tool. 

%An automated verification of the well known
%modal logic cube in Isabelle/HOL is presented. In contrast to related
%work, which achieved a similar result using encodings in first-order logic in 
%combination with first-order automated theorem provers, the solution presented here is
%more elegant, transparent and effective. This solution employs an
%embedding of quantified modal logic in classical higher-order
%logic. Automated reasoning tools, such as Sledgehammer with LEO-II,
%Satallax and CVC4, Metis and Nitpick, are employed to achieve full automation.
%Though successful, the experiments also motivate some technical improvements 
%in the Isabelle/HOL tool. 
\end{abstract} *}


section {* Introduction *}

text {* We present an approach to meta-reasoning about modal logics,
and apply it to verify the relative strengths of logics in the well-known \emph{modal logic cube},
which is illustrated in Figure 1. In particular, proofs are given for the
equivalences of different axiomatizations and the inclusion relations shown in the cube.

\begin{figure}[tp]
\centering
\scalebox{0.8}{
\begin{tikzpicture}[thick,node/.style={rectangle,draw,font=\Large\bfseries}]

  % 1. Ebene
  \node[node] (K)   {K};
  \node[node] (K4)  [above right=2cm and 2cm of K.center,anchor=center] {K4};
  \node[node] (K5)  [below right=0.9cm and 1.6cm of K4.center,anchor=center] {K5};
  \node[node] (KB)  [right=8cm of K.center,anchor=center] {KB};
  \node[node] (K45) [right=5cm of K4.center,anchor=center] {K45};
  \node[node] (KB5) [above right=2cm and 2cm of KB.center,anchor=center] {KB5};

  % 2. Ebene
  \node[node] (D)  [above=4cm of K.center,anchor=center] {D};
  \node[node] (D4) [above right=2cm and 2cm of D.center,anchor=center] {D4};
  \node[node] (D5) [below right=0.9cm and 1.6cm of D4.center,anchor=center] {D5};
  \node[node] (DB) [right=8cm of D.center,anchor=center] {DB};
  \node[node] (D45)[right=5cm of D4.center,anchor=center] {D45};

  % 3. Ebene
  \node[node] (M)  [above=4cm of D.center,anchor=center] {M};
  \node[node] (S4) [above right=2cm and 2cm of M.center,anchor=center] {S4};
  \node[node] (B)  [right=8cm of M.center,anchor=center] {B};
  \node[node] (B)  [right=8cm of M.center,anchor=center] {B};
  \node[node] (S5) [above right=2cm and 2cm of B.center,anchor=center] {S5};

  \node[align=center,font=\Large\bfseries] [right=0.1cm of S5.north east,anchor=north west]
   {\begin{tabular}{ l }
     $\equiv$ M5 $\equiv$ MB5 $\equiv$ M4B5\\
     $\equiv$ M45 $\equiv$ M4B $\equiv$ D4B\\
     $\equiv$ D4B5 $\equiv$ DB5
    \end{tabular}
    };
  \node[align=left,font=\large\bfseries] [above right=1.75cm and 3cm of D45.north east,anchor=north west]
   {
   \begin{tabular}{ l l }
      M: & $\nec P \rightarrow P$ \\
      B: & $P \rightarrow \nec\pos P$ \\
      D: & $\nec P \rightarrow \pos P$ \\
      4: & $\nec P \rightarrow \nec\nec P$ \\
      5: & $\pos P \rightarrow \nec\pos P$
   \end{tabular}
   };

  \node[draw=none,fill=none,font=\large\bfseries] (K1) [below right=2.5cm and 3.25cm of D45.south east,anchor=north west] {K};
  \node[draw=none,fill=none,font=\large\bfseries] (M1) [above=2cm of K1.center,anchor=center] {M};
  \node[draw=none,fill=none,font=\large\bfseries] (41) [above right=1.25cm and 1.25cm of K1.center,anchor=center] {4};
  \node[draw=none,fill=none,font=\large\bfseries] (51) [above right=0.75cm and 1.75cm of K1.center,anchor=center] {5};
  \node[draw=none,fill=none,font=\large\bfseries] (B1) [right=2cm of K1.center,anchor=center] {B};
   
  \node[align=center,font=\Large\bfseries] [right=0.1cm of KB5.north east,anchor=north west]
   {$\equiv$ K4B5 $\equiv$ K4B};
  \path[->,>=stealth',thick,every node/.style={font=\large}]
    (K1)  edge (M1)
          edge (41)
          edge (51)
          edge (B1);

  \path[->,>=stealth',thick,every node/.style={font=\large}]
    (K)   edge (K4)
          edge (K5)
          edge (KB)
          edge (D)
    (K4)  edge (K45)
          edge (D4)
    (K5)  edge (K45)
          edge (D5)
    (KB)  edge (KB5)
          edge (DB)
    (K45) edge (KB5)
          edge (D45)
    (KB5) edge (S5)

    (D)   edge (D4)
          edge (D5)
          edge (DB)
          edge (M)
    (D4)  edge (D45)
          edge (S4)
    (D5)  edge (D45)
    (DB)  edge (B)
    (D45) edge (S5)

    (M)  edge (S4)
         edge (B)
    (S4) edge (S5)
    (B)  edge (S5);
    
\end{tikzpicture}
}
\caption{The modal logic cube: 
reasoning in modal logics is commonly done with
respect to a certain set of basic axioms; different choices of basic
axioms give rise to different modal logics. These modal logics can be
arranged as vertices in a cube, such that the edges between them
denote inclusion relations.
}
\label{fig1}
\end{figure}

Our solution makes extensive use of the fact that all modal logics found in the cube
are sound and complete because they arise from base modal logic K by adding Sahlqvist axioms.
This is in contrast to prior work by Rabe et al.~\cite{Rabe}, who address the more general problem of determining the
relation between two arbitrary modal logics characterized by their sets of inference
rules. In their article the authors apply first-order logic encodings in combination with first-order
automated theorem provers to prove an inclusion relation employing a number of different decision strategies.
For the subproblem of only comparing logics within the cube (and therefore taking advantage of normality as additional knowledge)
our solution improves on the elegance and simplicity of the problem encodings, as well as with automation performance.
One motivation of this paper is to demonstrate the advantage of a pragmatically more expressive logic
environment (here classical higher-order logic) in comparison to a less expressive language such as
first-order logic or decidable fragments thereof.

We exploit an embedding of quantified multimodal
logic (QML) in classical higher-order logic (HOL) \cite{J23}, in which we carry out the
automated verification of the aforementioned inclusion relations. These include the logics \textbf{K}, \textbf{D},
\textbf{M} (also known as \textbf{T}), \textbf{S4}, and
\textbf{S5}. We analyze inclusion and equivalence
relations for modal logics that can be defined from normal modal logic
\textbf{K} by adding (combinations of) the axioms M, B, D, 4, and
5. In our problem encodings we exploit the well-known correspondences
between these axioms and semantic properties of accessibility
relations (i.e. Kripke models). These correspondences can themselves be elegantly formalized
and effectively automated in our approach. Formalization of the modal
axioms M, B, D, 4, and 5 requires quantification over propositional
variables. This explains why an embedding of \textit{quantified} modal
logic in HOL is needed here, and not simply an embedding of propositional
modal logic in HOL.

%In a sense, this paper provides a response to a related article by
%Rabe et al.~\cite{Rabe}. In their article the authors apply
%first-order logic encodings in combination with first-order automated
%theorem provers to verify the modal logic cube. 
%Our solution achieves significant improvements, most
%notably with respect to elegance and simplicity of the problem
%encodings, as well as with automation performance. One
%motivation of this paper is to demonstrate the
%advantage of a pragmatically more expressive logic environment (here
%classical higher-order logic) in comparison to a less expressive
%language such as first-order logic or decidable fragments thereof.

Our previous work (see the non-refereed, invited paper \cite{B12}) has
already demonstrated the feasibility of the approach. However, instead
of the development done there in pure TPTP THF~\cite{C25},
we here work with Isabelle/HOL~\cite{Nipkow-Paulson-Wenzel:2002} as the base
environment, and fruitfully exploit various reasoning
tools that are provided with it. This includes the
Sledgehammer-based \cite{EasyChair:128} interfaces from Isabelle/HOL to
the external higher-order theorem provers LEO-II~\cite{C26} and
Satallax~\cite{Satallax}, as well as Isabelle/HOL's own reasoner
Metis~\cite{hurd2003d}. Moreover, the higher-order model finding capabilities
of Nitpick~\cite{BlanchetteN-ITP10} are heavily used in order to formulate
and prove subsequent inclusion theorems in Isabelle/HOL.
We also encountered some problems with interacting with the proof
reconstruction available for LEO-II and Satallax in Isabelle/HOL.

This paper is a verified document in
the sense that it has been automatically generated from Isabelle/HOL
source code with the help of Isabelle's \textit{build} tool (the
entire source package is available from
\url{http://christoph-benzmueller.de/varia/pxtp2015.zip}).

The paper is structured as follows: Section~\ref{sec1} presents an
encoding of QML in HOL. This part reuses the theory provided by
Benzm\"uller and Paulson~\cite{J23}, which has recently been further
developed (to cover full higher-order QML) and applied for the verification of
G\"odel's ontological argument~\cite{GoedelGod-AFP,ECAI}. Section~\ref{sec2}
first establishes the well-known correspondence between properties of models
and base axioms, and then investigates the equivalence of different axiomatizations.
Subsequently, all inclusion relations as depicted in the modal logic cube are shown to be proper. Finally, 
the minimal number of possible worlds that is required to obtain proper inclusions in each case 
is determined and verified. Section~\ref{sec:eval} presents a short evaluation and discussion of the 
conducted experiments, and Section~\ref{sec:conc} concludes the paper.
*}

section {* An Embedding of Quantified Multimodal Logics in HOL \label{sec1} *}

text{* In contrast to the monomodal case, in quantified multimodal logics both modalities @{text "\<box>"} and @{text "\<diamond>"}
are parametrized, such that they refer to potentially different accessibility relations. We write
@{text "\<box>\<^sup>R"} and @{text "\<diamond>\<^sup>R"} to refer to necessity and possibility wrt.\ a relation $R$. Furthermore, in terms of quantification,
we only consider the constant-domain case: this means that all possible worlds share one common domain
of discourse. More details on the embedding of QML in HOL are given in earlier work~\cite{J23,ECAI}. *} 

(*<*) 

typedecl i		     -- "the type for possible worlds"  

(*>*) 
text {* QML formulas are translated as HOL terms of type @{typ "i \<Rightarrow> bool"}, where @{typ i} is the type of possible worlds.
This type is abbreviated as @{text "\<sigma>"}. *}
(*<*) 

type_synonym \<sigma> = "(i \<Rightarrow> bool)"

(*>*)  
text {* The classical connectives $\neg, \wedge, \rightarrow$, and $\forall$
(which quantifies over individuals and over sets of individuals) and $\exists$ (over individuals) are
lifted to type $\sigma$. The lifted connectives are @{text "\<not>\<^sup>m"}, @{text "\<and>\<^sup>m"}, @{text "\<or>\<^sup>m"}, 
@{text "\<rightarrow>\<^sup>m"}, @{text "\<equiv>\<^sup>m"}, @{text "\<forall>"}, and @{text "\<exists>"} (the latter two are modeled as constant symbols). 
Other connectives can be introduced analogously. Moreover, the modal 
operators @{text "\<box>"} and @{text "\<diamond>"}, parametric to @{text "R"},  are introduced.
Note that in symbols like @{text "\<not>\<^sup>m"}, symbol @{text "m"} is simply part of the name,
whereas in @{text "\<box>\<^sup>R"} and @{text "\<diamond>\<^sup>R"}, symbol @{text "R"} is a parameter to the modality.
 *}

abbreviation mnot :: "\<sigma> \<Rightarrow> \<sigma>" (*<*)("\<not>\<^sup>m")(*>*) where "\<not>\<^sup>m \<phi> \<equiv> (\<lambda>w. \<not> \<phi> w)"    
abbreviation mand :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<and>\<^sup>m" 52)(*>*) where "\<phi> \<and>\<^sup>m \<psi> \<equiv> (\<lambda>w. \<phi> w \<and> \<psi> w)"   
abbreviation mor :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<or>\<^sup>m" 51)(*>*) where "\<phi> \<or>\<^sup>m \<psi> \<equiv> (\<lambda>w. \<phi> w \<or> \<psi> w)"   
abbreviation mimplies :: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<rightarrow>\<^sup>m" 49)(*>*) where "\<phi> \<rightarrow>\<^sup>m \<psi> \<equiv> (\<lambda>w. \<phi> w \<longrightarrow> \<psi> w)"  
abbreviation mequiv:: "\<sigma> \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)(infixr "\<equiv>\<^sup>m" 48)(*>*) where "\<phi> \<equiv>\<^sup>m \<psi> \<equiv> (\<lambda>w. \<phi> w \<longleftrightarrow> \<psi> w)"  
abbreviation mforall :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*)("\<forall>")(*>*) where "\<forall> \<Phi> \<equiv> (\<lambda>w. \<forall>x. \<Phi> x w)"   
abbreviation mexists :: "('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma>" (*<*)("\<exists>")(*>*) where "\<exists> \<Phi> \<equiv> (\<lambda>w. \<exists>x. \<Phi> x w)"
abbreviation mbox :: "(i \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)("\<box>\<^sup>_ _")(*>*) where "\<box>\<^sup>R \<phi> \<equiv> (\<lambda>w. \<forall>v. (R w v) \<longrightarrow> \<phi> v)"
abbreviation mdia :: "(i \<Rightarrow> i \<Rightarrow> bool) \<Rightarrow> \<sigma> \<Rightarrow> \<sigma>" (*<*)("\<diamond>\<^sup>_ _")(*>*) where "\<diamond>\<^sup>R \<phi> \<equiv> (\<lambda>w. \<exists>v. R w v \<and> \<phi> v)" 

text {* For grounding lifted formulas, the meta-predicate @{text "[\<cdot>]"}, read @{text "valid"}, is introduced. *}

(*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
abbreviation valid :: "\<sigma> \<Rightarrow> bool" (*<*)("[_]")(*>*) where "[p] \<equiv> \<forall>w. p w"


section {* Reasoning about Modal Logics \label{sec2} *}

subsection {* Correspondence Results *}           

text {* Axioms of the modal cube correspond to constraints on the underlying accessibility relations.
These constraints are as follows: *}

(*<*) hide_const refl sym trans (*>*)

definition "refl \<equiv> \<lambda>R :: (i \<Rightarrow> i \<Rightarrow> bool). \<forall>S. R S S"                                                         -- {* reflexivity *}
definition "sym \<equiv> \<lambda>R :: (i \<Rightarrow> i \<Rightarrow> bool). \<forall>S T. (R S T \<longrightarrow> R T S)"                                -- {* symmetry *}
definition "ser \<equiv> \<lambda>R :: (i \<Rightarrow> i \<Rightarrow> bool). \<forall>S. \<exists>T. R S T"                                                  -- {* seriality *}
definition "trans \<equiv> \<lambda>R :: (i \<Rightarrow> i \<Rightarrow> bool). \<forall>S T U. (R S T \<and> R T U \<longrightarrow> R S U)"           -- {* transitivity *}
definition "eucl \<equiv> \<lambda>R :: (i \<Rightarrow> i \<Rightarrow> bool). \<forall>S T U. (R S T \<and> R S U \<longrightarrow> R T U)"             -- {* Euclidean *} 


text {* The corresponding axioms are defined next; note that they are parametric over accessibility 
relation $R$: *}

definition "M \<equiv> \<lambda>R . valid (\<forall>(\<lambda>P. (\<box>\<^sup>R P) \<rightarrow>\<^sup>m P))"
definition "B \<equiv> \<lambda>R . valid (\<forall>(\<lambda>P. P \<rightarrow>\<^sup>m \<box>\<^sup>R\<diamond>\<^sup>R P))"
definition "D \<equiv> \<lambda>R . valid (\<forall>(\<lambda>P. (\<box>\<^sup>R P) \<rightarrow>\<^sup>m \<diamond>\<^sup>R P))"
definition "IV \<equiv> \<lambda>R . valid (\<forall>(\<lambda>P. (\<box>\<^sup>R P) \<rightarrow>\<^sup>m \<box>\<^sup>R\<box>\<^sup>R P))"
definition "V \<equiv> \<lambda>R . valid (\<forall>(\<lambda>P. (\<diamond>\<^sup>R P) \<rightarrow>\<^sup>m \<box>\<^sup>R\<diamond>\<^sup>R P))"

text {* We will see below that \emph{correspondence theorems} (between axioms and constraints on accessibility relations)
can be elegantly expressed in HOL by exploiting the embedding used above.
These correspondence theorems link a constraint to every axiom---for instance, $M$ is linked to $\mathit{refl}$.
%Furthermore, the constraint has to be met by its every model (e.g. accessibility relation).
Subsequently, in order to make statements about the relationship of two logics in the cube, it is sufficient to only look at the model constraints of their
respective axiomatizations. Throughout the rest of this paper, all reasoning will be done on the model-theoretic
side and then interpreted on the proof-theoretic side by the means of this correspondence. *}

(*<*)
sledgehammer_params [verbose=true]
(*>*)

subsubsection {* Axiom M corresponds to Reflexivity *}

theorem A1: "(\<forall>R. (refl R) \<longleftrightarrow> (M R))" by (metis M_def refl_def)

subsubsection {* Axiom B corresponds to Symmetry *}

lemma A2_a: "(\<forall>R. (sym R) \<longrightarrow> (B R))" by (metis B_def sym_def)
lemma A2_b:  "(\<forall>R. (B R) \<longrightarrow> (sym R))" by (simp add:B_def sym_def, force)
theorem A2: "(\<forall>R. (sym R) \<longleftrightarrow> (B R))" by (metis A2_a A2_b)

subsubsection {* Axiom D corresponds to Seriality *}

theorem A3: "(\<forall>R. (ser R) \<longleftrightarrow> (D R))" by (metis D_def ser_def)

subsubsection {* Axiom 4 corresponds to Transitivity *}

theorem A4: "(\<forall>R. (trans R) \<longleftrightarrow> (IV R))" by (metis IV_def trans_def)

subsubsection {* Axiom 5 corresponds to Euclideanness *}

lemma A5_a: "(\<forall>R. (eucl R) \<longrightarrow> (V R))" by (metis V_def eucl_def)
lemma A5_b: "(\<forall>R. (V R) \<longrightarrow> (eucl R))" by (simp add:V_def eucl_def, force)
theorem A5: "(\<forall>R. (eucl R) \<longleftrightarrow> (V R))" by (metis A5_a A5_b)

subsubsection {* Correspondence of McKinsey Axiom *}

definition "McK \<equiv> \<lambda>R . valid (\<forall>(\<lambda>P. (\<diamond>\<^sup>R\<box>\<^sup>R P) \<rightarrow>\<^sup>m \<box>\<^sup>R\<diamond>\<^sup>R P))"
definition "McKCond \<equiv> \<lambda>R::(i \<Rightarrow>i\<Rightarrow>bool). 
\<forall>P. ((\<forall>W. \<exists>V. (R W V \<and>  P V))
     \<longrightarrow> (\<exists>V. \<forall>W. (R W V \<longrightarrow> P V)))" 

lemma A6_a: "(\<forall>R. (McK R) \<longrightarrow> (McKCond R))" by (metis McKCond_def)
lemma A6_b: "(\<forall>R. (McKCond R) \<longrightarrow> (McK R))" nitpick oops (* this fails *)

subsubsection {* Correspondence of Löb Axiom *}

definition "Loeb \<equiv> \<lambda>R . valid (\<forall>(\<lambda>P. ((\<box>\<^sup>R ((\<box>\<^sup>R P) \<rightarrow>\<^sup>m P))) \<rightarrow>\<^sup>m (\<box>\<^sup>R P)))"
definition "UpWellFounded \<equiv> 
\<lambda>R::(i\<Rightarrow>i\<Rightarrow>bool). (\<forall>X Z. ((X Z) \<longrightarrow> (\<exists> Y. ((X Y) \<and> (\<forall> W. ((R Y Y) \<longrightarrow> \<not>(X W)))))))" 

lemma A6_a: "(\<forall>R. (Loeb R) \<longrightarrow> (UpWellFounded R))" sledgehammer [remote_leo2 remote_satallax]
lemma A6_b: "(\<forall>R. (Loeb R) \<longrightarrow> (trans R))" nitpick
lemma A6_c: "(\<forall>R. ((UpWellFounded R) \<and> (trans R)) \<longrightarrow> (Loeb R))" nitpick

subsection {* Alternative Axiomatisations of Modal Logics *} 

text {* Often the same logic within the cube can be obtained through different axiomatizations.
In this section we show how to prove different axiomatizations for logic \textbf{S5} resp. \textbf{KB5} to be equivalent. Using the
correspondence theorems from the previous section, the equivalences can be elegantly formulated solely using the properties
of accessibility relations. In Subsections~\ref{M5-and-MB5} and~\ref{M5-and-M4B5} we also add the corresponding 
statements using the modal logic axioms; this could analogously be done also for the other theorems and lemmata 
presented in Sections {{3.2 and 3.3}}.

The theorems below can be solved directly by Metis when it is provided the 
minimal set of necessary definitions. Sledgehammer (with the ATPs LEO-II and Satallax or with first-order provers) can also 
quickly solve these problems, in which case the manual selection of the required definitions is not necessary. *}

subsubsection {* M5 $\Longleftrightarrow$ MB5 \label{M5-and-MB5}*}
theorem B1: "\<forall>R.((refl R) \<and> (eucl R)) \<longleftrightarrow> ((refl R) \<and> (sym R) \<and> (eucl R))"
 by (metis eucl_def refl_def sym_def) 
theorem B1_alt: "\<forall>R.((M R) \<and> (V R)) \<longleftrightarrow> ((M R) \<and> (B R) \<and> (V R))"
 by (metis A1 A2 A5 B1)

subsubsection {* M5 $\Longleftrightarrow$ M4B5 \label{M5-and-M4B5}*}
theorem B2: "\<forall>R.((refl R) \<and> (eucl R)) \<longleftrightarrow> ((refl R) \<and> (trans R) \<and> (sym R) \<and> (eucl R))"
 by (metis eucl_def refl_def trans_def sym_def)
theorem B2_alt: "\<forall>R.((M R) \<and> (V R)) \<longleftrightarrow> ((M R) \<and> (IV R) \<and> (B R) \<and> (V R))"
 by (metis A1 A4 A5 B1_alt B2)

subsubsection {* M5 $\Longleftrightarrow$ M45 *}
theorem B3: "\<forall>R.((refl R) \<and> (eucl R)) \<longleftrightarrow> ((refl R) \<and> (trans R) \<and> (eucl R))" 
 by (metis eucl_def refl_def trans_def)

subsubsection {* M5 $\Longleftrightarrow$ M4B *}
theorem B4: "\<forall>R.((refl R) \<and> (eucl R)) \<longleftrightarrow> ((refl R) \<and> (trans R) \<and> (sym R))"
 by (metis eucl_def refl_def sym_def trans_def)
                                        
subsubsection {* M5 $\Longleftrightarrow$ D4B *}
theorem B5: "\<forall>R.((refl R) \<and> (eucl R)) \<longleftrightarrow> ((ser R) \<and> (trans R) \<and> (sym R))"
 by (metis eucl_def refl_def ser_def sym_def trans_def)

subsubsection {* M5 $\Longleftrightarrow$ D4B5 *}
theorem B6: "\<forall>R.((refl R) \<and> (eucl R)) \<longleftrightarrow> ((ser R) \<and> (trans R) \<and> (sym R) \<and> (eucl R))"
 by (metis eucl_def refl_def ser_def sym_def trans_def)

subsubsection {* M5 $\Longleftrightarrow$ DB5 *}
theorem B7: "\<forall>R.((refl R) \<and> (eucl R)) \<longleftrightarrow> ((ser R) \<and> (sym R) \<and> (eucl R))"
 by (metis eucl_def refl_def ser_def sym_def)

subsubsection {* KB5 $\Longleftrightarrow$ K4B5 *}
theorem B8: "\<forall>R.((sym R) \<and> (eucl R)) \<longleftrightarrow> ((trans R) \<and> (sym R) \<and> (eucl R))"
 by (metis eucl_def sym_def trans_def)

subsubsection {* KB5 $\Longleftrightarrow$ K4B *}
theorem B9: "\<forall>R.((sym R) \<and> (eucl R)) \<longleftrightarrow> ((trans R) \<and> (sym R))"
 by (metis eucl_def sym_def trans_def)


subsection {* Proper Inclusion Relations between Different Modal Logics *}

text {* An edge within the cube denotes an inclusion between the connected logics. In the forward direction, these can
be trivially shown valid through monotonicity of entailment and equivalence of the different
axiomatizations. For example, for the forward link from logic \textbf{K} to logic \textbf{B}, we need to show that every 
theorem of \textbf{K} is also a theorem of \textbf{B}; this simply means to
disregard the additional axiom B.
 Below, the crucial backward directions are proved. 
Informally, it is shown that through moving further
up in the cube (adding further axioms), theorems can be proved which were not provable before; this means
that the inclusions are proper.
We write $A > B$ to indicate that logic $A$ can prove strictly more theorems than logic $B$.

It has to be noted that some logics are actually equivalent if the only models considered have few
enough worlds; examples are given below. We introduce some useful abbreviations to formulate
constraints on the number of worlds in a model.*}


abbreviation one_world_model :: "i \<Rightarrow> bool" (*<*)("#\<^sup>1")(*>*)
  where "#\<^sup>1 w1 \<equiv> \<forall>x. x = w1"
abbreviation two_world_model :: "i \<Rightarrow> i \<Rightarrow> bool" (*<*)("#\<^sup>2")(*>*)
  where "#\<^sup>2 w1 w2 \<equiv> (\<forall>x. x = w1 \<or> x = w2) \<and> w1 \<noteq> w2" 
abbreviation three_world_model :: "i \<Rightarrow> i \<Rightarrow> i \<Rightarrow> bool" (*<*)("#\<^sup>3")(*>*)
  where "#\<^sup>3 w1 w2 w3 \<equiv> (\<forall>x. x = w1 \<or> x = w2 \<or> x = w3) \<and> w1 \<noteq> w2 \<and> w1 \<noteq> w3 \<and> w2 \<noteq> w3" 

text {*In what follows, we reserve the symbols \emph{i1}, \emph{i2} and \emph{i3} for worlds, and \emph{r} for an accessibility relation.*}
(*<*)
consts i1::"i" i2::"i" i3::"i" r:: "i \<Rightarrow> i \<Rightarrow> bool"
(*>*)
text {*
We applied the following methodology in the experiments reported in this section:

\begin{description}
\item[\textbf{(Step A)}] First we deliberately made invalid conjectures about inclusion relations---e.g. for proving 
K4 $>$ K we first wrongly conjectured that K4 $\subseteq$ K, meaning that K4 entails K. 
We did this by conjecturing 
\begin{center} @{text "lemma C1_A: \<forall>R. (trans R)"} \end{center}
These wrongly-conjectured lemmata in Step A are uniformly named @{text "C*_A"}.
Note that for the formulation of the @{text "C*_A"}-lemmata we again exploit the correspondence results given earlier, 
and we work with conditions on the accessibility relations instead of using the corresponding modal logic axioms.
For each @{text "C*_A"}-lemma Nitpick quickly generates a countermodel, which 
it communicates in a specific syntax. For example, the countermodel it presents for @{text "C1_A"} is 
\begin{center}
@{text "
R = (\<lambda>x. _)(i\<^sub>1 := (\<lambda>x. _)(i\<^sub>1 := True, i\<^sub>2 := True), i\<^sub>2 := (\<lambda>x. _)(i\<^sub>1 := True, i\<^sub>2 := False))
"}.
\end{center}
Diagrammatically this 2-world countermodel can be represented as follows 
\begin{center}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
          edge [bend left] node {} (i_2)
    (i_2) edge [bend left] node {} (i_1);
\end{tikzpicture}
\end{center}

\item[\textbf{(Step B)}] Next, we systematically employed the arity information obtained from the countermodels for the @{text "C*_A"}-lemmata, reported by Nitpick,
to formulate a corresponding 
lemma to be passed via Sledgehammer to the HOL-ATPs LEO-II, Satallax and/or CVC4 \cite{CVC4} (whenever it was not trivially provable by the automation 
tools @{text "simp"}, @{text "force"} and/or @{text "blast"} available within Isabelle/HOL).
In our running example this lemma is 
\begin{center}
 @{text "C1_B: #\<^sup>2 i1 i2 \<longrightarrow> \<forall>R. \<not> trans R"}
\end{center}
 All but four of these lemmata can actually be proved by either LEO-II or Satallax. Some of the easier problems can already be automated with 
 @{text "simp"}, @{text "force"} and  @{text "blast"}, which are preferred here.  
 The four cases in which no automation attempts succeeded (we also tried all other integrated ATPs in Isabelle) 
 are named @{text "C*_ATP_challenge"} below.
 Moreover, there are ten problems named @{text "C*_Isabelle_challenge"}. For these problems LEO-II or Satallax found proofs, but their
 Metis-based integration into Isabelle failed. Hence, no verification was obtained for these problems. However, we found that 
 five of these @{text "C*_Isabelle_challenge"} problems can also be proved by CVC4, for which proof integration
 worked. 
 Unfortunately, no other automation means (including the integrated first-order ATPs or SMT solvers) succeeded for the
 @{text "C*_Isabelle_challenge"} problems.

\item[\textbf{(Step C)}] For the verification of the modal logic cube, the non-proved or non-integrated @{text "C*_challenge"} problems of Step B are clearly unsatisfactory, since
no proper verification in Isabelle is obtained. However, an easy solution for these (and all other) cases
is possible by exploiting not only Nitpick's arity information on the countermodels, but by using all the information about the 
countermodels it presents, that is, the precise information on the accessibility relation. 
For example, Nitpick's countermodel for @{text "C1_A"} from above 
can be converted into the following theorem
(where @{text r} denotes a fixed accessibility relation) 
\begin{center}
@{text "theorem C1_C: #\<^sup>2 i1 i2 \<and> r i1 i1 \<and> r i1 i2 \<and> r i2 i1 \<and> \<not>r i2 i2 \<longrightarrow> \<not> trans r"}. 
\end{center}
The resulting theorems we generate 
are uniformly named @{text "C*_C"}. It turns out that all  @{text "C*_C"}-theorems can be quickly verified in Isabelle by Metis. 
Thus, for each link in the modal logic we provide either a verified @{text "C*_B"} theorem or, if this was not successful, a verified @{text "C*_C"} 
theorem. Taken together, this confirms that the inclusion relation in the cube are indeed proper. 
Hence, these @{text "C*_B"} resp. @{text "C*_C"} theorems complete the verification of the modal logic cube. Below the 
@{text "C*_C"} proof attempts are omitted if the corresponding @{text "C*_B"} attempts were already successful.

 
\item[\textbf{(Step D)}] We additionally prove that the countermodels found by Nitpick in Step A are minimal (regarding the number 
of possible worlds). In other words, we prove here that the world model constraints as exploited in Step B are in fact minimal constraints
under which the inclusion relations can be shown to be proper. Of course, if such a countermodel consists of one possible world only, nothing 
needs to be shown. 
\end{description}

Note that the entire process sketched above, that is the schematic Steps A-D, could be fully automated, meaning that the formulation of the lemmata and theorems
in each step could be obtained automatically by analyzing and converting Nitpick's output.
In our experiments we still wrote and invoked the verification of each link in the 
modal cube manually however. Clearly, automation facilities could be very useful for the exploration of the meta-theory of other logics, for
example, conditional logics~\cite{IJCAI}, since the overall methodology is obviously transferable to other logics of interest.
*}

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
          edge [bend left] node {} (i_2)
    (i_2) edge [bend left] node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* K4 $>$ K *}

lemma C1_A: "\<forall>R. trans R" nitpick oops
theorem C1_B: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. trans R)" by (simp add:trans_def, force)
lemma C1_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. trans R)" by (metis (lifting, full_types) trans_def) 

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_2) edge [loop above] node {} ()
          edge node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* K5 $>$ K *}

lemma C2_A: "\<forall>R. eucl R" nitpick oops
theorem C2_B: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. eucl R)" by (simp add:eucl_def, force)
lemma C2_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. eucl R)" by (metis (lifting, full_types) eucl_def) 

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_2) edge node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* KB $>$ K *}

lemma C3_A: "\<forall>R. sym R" nitpick oops
theorem C3_B: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. sym R)" by (simp add:sym_def, force)
lemma C3_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. sym R)" by (metis (full_types) sym_def) 

subsubsection {* K45 $>$ K4 *}

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [bend left] node {} (i_2)
    (i_2) edge [bend left] node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}

lemma C4_A: "\<forall>R. ser R \<longrightarrow> (ser R \<and> eucl R)" nitpick oops
lemma C4_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. ser R \<longrightarrow> (ser R \<and> eucl R))"  
-- {*sledgehammer [remote\_leo2](ser\_def eucl\_def)*}
-- {*CPU time: 13.74 s. Metis reconstruction failed.*}
-- {*sledgehammer [cvc4,timeout=300] -- timed out*} oops
theorem C4_C: "#\<^sup>2 i1 i2  \<and> \<not>r i1 i1 \<and> r i1 i2 \<and> r i2 i1 \<and> \<not>r i2 i2 \<longrightarrow> \<not> (ser r \<longrightarrow> (ser r \<and> eucl r))" 
 by (metis ser_def eucl_def)
lemma C4_D: "#\<^sup>1 i1  \<longrightarrow> (\<forall>R. ser R \<longrightarrow> (ser R \<and> eucl R))" by (metis (full_types) eucl_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$};
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* K45 $>$ K5 *}

lemma C5_A: "\<forall>R. eucl R \<longrightarrow> (ser R \<and> eucl R)" 
 nitpick oops
lemma C5_B_Isabelle_challenge: "#\<^sup>1 i1 \<longrightarrow> \<not> (\<forall>R. (eucl R) \<longrightarrow> (ser R) \<and> (eucl R))" 
-- {*sledgehammer [remote\_leo2](eucl\_def ser\_def) -- CPU time: 14.61 s. Metis reconstruction failed.*} 
-- {*sledgehammer [cvc4,timeout=300] -- timed out*} oops
theorem C5_C: "#\<^sup>1 i1 \<and> \<not>r i1 i1 \<longrightarrow> \<not> (eucl r \<longrightarrow> (ser r \<and> eucl r))" by (metis (full_types) eucl_def ser_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} () 
          edge [bend left] node {} (i_2) 
    (i_2) edge [bend left] node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* KB5 $>$ KB *}

lemma C6_A: "\<forall>R. sym R \<longrightarrow> (sym R \<and> eucl R)" 
 nitpick oops
lemma C6_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. sym R \<longrightarrow> (sym R \<and> eucl R))"
-- {*sledgehammer [remote\_leo2,timeout=200](sym\_def eucl\_def) -- CPU time: 29.0 s. Metis reconstruction failed. *}
-- {*sledgehammer [cvc4,timeout=300] suggested following line:*}
 by (metis (full_types) A4 B8 C1_B IV_def sym_def) (* theorem C6_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> r i1 i2 \<and> r i2 i1 \<and> \<not> r i2 i2 \<longrightarrow> \<not> (sym r \<longrightarrow> (sym r \<and> eucl r))" by (metis (full_types) eucl_def sym_def) *)
lemma C6_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. sym R \<longrightarrow> (sym R \<and> eucl R))"
 by (metis (full_types) eucl_def)

text {*
\begin{isbfig}{8em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
    (i_2) edge node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* KB5 $>$ K45 *}

lemma C7_A: "\<forall>R. ser R \<and> eucl R \<longrightarrow> (sym R \<and> eucl R)" 
 nitpick oops
lemma C7_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. ser R \<and> eucl R \<longrightarrow> (sym R \<and> eucl R))"
-- {*sledgehammer [remote\_leo2] (ser\_def eucl\_def sym\_def) -- CPU time: 11.15 s. Metis reconstruction failed.*} 
-- {*sledgehammer [cvc4,timeout=300] -- timed out*} oops 
theorem C7_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> \<not> r i1 i2 \<and> r i2 i1 \<and> \<not> r i2 i2 \<longrightarrow> \<not> (ser r \<and> eucl r \<longrightarrow> (sym r \<and> eucl r))" 
 by (metis (full_types) ser_def eucl_def sym_def)
lemma C7_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. ser R \<and> eucl R \<longrightarrow> (sym R \<and> eucl R))" by (metis (full_types) sym_def) 

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* D $>$ K *}

lemma C8_A: "\<forall>R. ser R" nitpick oops
lemma C8_B: "#\<^sup>1 i1 \<longrightarrow> \<not>(\<forall>R. (ser R))" by (simp add:ser_def, force)
theorem C8_C: "#\<^sup>1 i1 \<and> \<not>r i1 i1 \<longrightarrow> \<not>(ser r)" by (metis (full_types) ser_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* D4 $>$ K4 *}

lemma C9_A: "\<forall>R. trans R \<longrightarrow> (ser R \<and> trans R)" 
 nitpick oops
theorem C9_B: "#\<^sup>1 i1 \<longrightarrow> \<not> (\<forall>R. trans R \<longrightarrow> (ser R \<and> trans R))" 
 using C1_D C8_B by blast 
 (* theorem C9_C: "#\<^sup>1 i1 \<and> \<not> r i1 i1 \<longrightarrow> \<not> (trans r \<longrightarrow> (ser r \<and> trans r))" 
 by (metis (full_types) ser_def trans_def) *)
 


text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* D5 $>$ K5 *}
lemma C10_A: "\<forall>R. eucl R \<longrightarrow> (ser R \<and> eucl R)" nitpick oops
theorem C10_B: "#\<^sup>1 i1  \<longrightarrow> \<not> (\<forall>R. eucl R \<longrightarrow> (ser R \<and> eucl R))" using B9 C3_D C9_B by blast (* theorem C10_C: "#\<^sup>1 i1 \<and> \<not> r i1 i1 \<longrightarrow> \<not> (eucl r \<longrightarrow> (ser r \<and> eucl r))" by (metis (full_types) ser_def eucl_def) *)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ();
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* D45 $>$ K45 *}

lemma C11_A: "\<forall>R. trans R \<and> eucl R \<longrightarrow> (ser R \<and> trans R \<and> eucl R)" 
 nitpick oops
theorem C11_B: "#\<^sup>1 i1 \<longrightarrow> \<not> (\<forall>R. trans R \<and> eucl R \<longrightarrow> (ser R \<and> trans R \<and> eucl R))"
 using B9 C3_D C9_B by blast (* theorem C11_C: "#\<^sup>1 i1 \<and> \<not> r i1 i1 \<longrightarrow> \<not> (trans r \<and> eucl r \<longrightarrow> (ser r \<and> trans r \<and> eucl r))" by (metis (full_types) ser_def eucl_def trans_def) *)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* DB $>$ KB *}

lemma C12_A: "\<forall>R. sym R \<longrightarrow> (ser R \<and> sym R)" 
 nitpick oops
theorem C12_B: "#\<^sup>1 i1 \<longrightarrow> \<not> (\<forall>R. sym R \<longrightarrow> (ser R \<and> sym R))" 
 using C11_B C3_D by blast 
(* theorem C12_easy: "#\<^sup>1 i1  \<and> \<not> r i1 i1 \<longrightarrow> \<not> (sym r \<longrightarrow> (ser r \<and> sym r))" by (metis (full_types) ser_def sym_def) *)

text {* 
\begin{isbfig}{9em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* S5 $>$ KB5 *}
lemma C13_A: "\<forall>R. sym R \<and> eucl R \<longrightarrow> (refl R \<and> eucl R)" 
 nitpick oops
theorem C13_B: "#\<^sup>1 i1 \<longrightarrow> \<not> (\<forall>R. sym R \<and> eucl R \<longrightarrow> (refl R \<and> eucl R))" using B5 C12_B C6_D by blast (* theorem C13_C: "#\<^sup>1 i1 \<and> \<not> r i1 i1 \<longrightarrow> \<not> (sym r \<and> eucl r \<longrightarrow> (refl r \<and> eucl r))" by (metis (full_types) sym_def eucl_def refl_def) *)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
          edge [bend left] node {} (i_2)
    (i_2) edge [bend left] node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* D4 $>$ D *}

lemma C14_A: "\<forall>R. (ser R) \<longrightarrow> (ser R) \<and> (trans R)" 
 nitpick oops
theorem C14_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not>(\<forall>R. ser R \<longrightarrow> (ser R \<and> trans R))"
-- {*sledgehammer [remote\_leo2] (ser\_def trans\_def) -- CPU time: 13.08 s. Metis reconstruction failed.*}
-- {*sledgehammer [cvc4,timeout=300] suggested following line: *}
 by (metis (full_types) C1_B trans_def ser_def) (* theorem C14_easy: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> r i1 i2 \<and> r i2 i1 \<and> \<not>r i2 i2 \<longrightarrow> \<not> (ser r \<longrightarrow> (ser r \<and> trans r))" by (metis ser_def trans_def) *)
lemma C14_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. ser R \<longrightarrow> (ser R \<and> trans R))" by (metis (full_types) trans_def) 

subsubsection {* D5 $>$ D *}
text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
    (i_2) edge [loop above] node {} () 
          edge node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}
lemma C15_A: "\<forall>R. ser R \<longrightarrow> (ser R \<and> eucl R)" 
 nitpick oops
theorem C15_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. ser R \<longrightarrow> (ser R \<and> eucl R))"
-- {*sledgehammer [remote\_leo2](ser\_def eucl\_def)*}
-- {*CPU time: 12.9 s. Metis reconstruction failed.*}
-- {*sledgehammer [cvc4,timeout=300] suggested following line: *}
 by (metis (full_types) C14_B_Isabelle_challenge trans_def eucl_def) (* theorem C15_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> r i1 i2 \<and> r i2 i1 \<and> \<not> r i2 i2 \<longrightarrow> \<not> (ser r \<longrightarrow> (ser r \<and> eucl r))" by (metis ser_def eucl_def) *)
lemma C15_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. ser R \<longrightarrow> (ser R \<and> eucl R))" by (metis (full_types) C2_D)


text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} () 
          edge node {} (i_2)
    (i_2) edge [loop above] node {} ();
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* DB $>$ D *}
lemma C16_A: "\<forall>R. ser R \<longrightarrow> (ser R \<and> sym R)" 
 nitpick oops

lemma C16_B: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. ser R \<longrightarrow> (ser R \<and> sym R))" by (simp add:ser_def sym_def, force) 
lemma C16_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. ser R \<longrightarrow> (ser R \<and> sym R))" by (metis (full_types) sym_def) 

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
          edge node {} (i_2)
    (i_2) edge [loop above] node {} ();
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* D45 $>$ D4 *}

lemma C17_A: "\<forall>R. ser R \<and> trans R \<longrightarrow> (ser R \<and> trans R \<and> eucl R)"
 nitpick oops

lemma C17_B_ATP_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not>(\<forall>R. ser R \<and> trans R \<longrightarrow> (ser R \<and> trans R \<and> eucl R))"
 oops -- {* All ATPs time out *}
theorem C17_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> r i1 i2 \<and> \<not> r i2 i1 \<and> r i2 i2 \<longrightarrow> \<not> (ser r \<and> trans r \<longrightarrow> (ser r \<and> trans r \<and> eucl r))" 
 by (metis (full_types) ser_def trans_def eucl_def)
lemma C17_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. ser R \<and> trans R \<longrightarrow> (ser R \<and> trans R \<and> eucl R))"
 by (metis (full_types) eucl_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
   \node[state] (i_3) [right=of i_2] {$i_3$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
          edge [bend left] node {} (i_2) 
    (i_2) edge [loop above] node {} () 
          edge [bend left] node {} (i_1) 
    (i_3) edge node {} (i_2);
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* D45 $>$ D5 *}

lemma C18_A: "\<forall>R. ser R \<and> eucl R \<longrightarrow> (ser R \<and> trans R \<and> eucl R)"
 nitpick oops

lemma C18_ATP_challenge: "#\<^sup>3 i1 i2 i3 \<longrightarrow> \<not> (\<forall>R. ser R \<and> eucl R \<longrightarrow> (ser R \<and> trans R \<and> eucl R))"
 oops -- {* All ATPs time out *}
theorem C18_C: "#\<^sup>3 i1 i2 i3 \<and> r i1 i1 \<and> r i1 i2 \<and> \<not> r i1 i3 \<and> r i2 i1 \<and> r i2 i2 \<and> \<not> r i2 i3 \<and> \<not> r i3 i1 \<and> r i3 i2 \<and> \<not> r i3 i3  \<longrightarrow> \<not> (ser r \<and> eucl r \<longrightarrow> (ser r \<and> trans r \<and> eucl r))" by (metis (full_types) eucl_def ser_def trans_def)
lemma C18_D: "#\<^sup>2 i1 i2 \<longrightarrow> (\<forall>R. ser R \<and> eucl R \<longrightarrow> (ser R \<and> trans R \<and> eucl R))"
 by (metis (full_types) eucl_def trans_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
    (i_2) edge node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* M $>$ D *}

lemma C19_A: "\<forall>R. ser R \<longrightarrow> refl R" 
 nitpick oops
theorem C19_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. ser R \<longrightarrow> refl R)"
-- {*sledgehammer [remote\_leo2,timeout=200] (ser\_def refl\_def) -- CPU time: 29.15 s. Metis reconstruction failed.*}
-- {*sledgehammer [cvc4,timeout=300] suggested following line: *}
 by (metis (full_types) C14_B_Isabelle_challenge trans_def refl_def) (* theorem C19_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> \<not> r i1 i2 \<and> r i2 i1 \<and> \<not> r i2 i2 \<longrightarrow> \<not> (ser r \<longrightarrow> refl r)" by (metis ser_def refl_def) *)
lemma C19_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. ser R \<longrightarrow> refl R)" by (metis (full_types) ser_def refl_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
    (i_2) edge node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* S4 $>$ D4 *}
lemma C20_A: "\<forall>R. ser R \<and> trans R \<longrightarrow> (refl R \<and> trans R)"
 nitpick oops

lemma C20_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. ser R \<and> trans R \<longrightarrow> (refl R \<and> trans R))"
-- {* sledgehammer [remote\_leo2](ser\_def trans\_def refl\_def) -- CPU time: 12.5 s. Metis reconstruction failed.*}
-- {*sledgehammer [cvc4,timeout=300] -- timed out*}
 oops
theorem C20_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> \<not> r i1 i2 \<and> r i2 i1 \<and> \<not> r i2 i2 \<longrightarrow> \<not> (ser r \<and> trans r \<longrightarrow> (refl r \<and> trans r))" 
 by (metis (full_types) ser_def refl_def trans_def)
lemma C20_D: "#\<^sup>1 i1  \<longrightarrow> (\<forall>R. ser R \<and> trans R \<longrightarrow> (refl R \<and> trans R))"
 by (metis (full_types) ser_def refl_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
    (i_2) edge node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}
subsubsection {* S5 $>$ D45 *}
lemma C21_A: "\<forall>R. ser R \<and> trans R \<and> eucl R \<longrightarrow> (refl R \<and> eucl R)" 
 nitpick oops

lemma C21_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. ser R \<and> trans R \<and> eucl R \<longrightarrow> (refl R \<and> eucl R))"
-- {*sledgehammer [remote\_leo2](ser\_def trans\_def eucl\_def refl\_def) -- CPU time: 12.51 s. Metis reconstruction failed. *}
-- {*sledgehammer [cvc4,timeout=300] -- timed out*}
 oops
theorem C21_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> \<not> r i1 i2 \<and> r i2 i1 \<and> \<not> r i2 i2 \<longrightarrow> \<not> (ser r \<and> trans r \<and> eucl r \<longrightarrow> (refl r \<and> eucl r))" 
 by (metis (full_types) ser_def trans_def eucl_def refl_def)
lemma C21_inclusion: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. ser R \<and> trans R \<and> eucl R \<longrightarrow> (refl R \<and> eucl R))"
 by (metis (full_types) ser_def refl_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} () 
          edge [bend left] node {} (i_2)
    (i_2) edge [bend left] node {} (i_1);
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* B $>$ DB *}

lemma C22_A: "\<forall>R. ser R \<and> sym R \<longrightarrow> (refl R \<and> sym R)" 
 nitpick oops
lemma C22_B_Isabelle_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. ser R \<and> sym R \<longrightarrow> (refl R \<and> sym R))"
-- {*sledgehammer [remote\_leo2,timeout=200](ser\_def sym\_def refl\_def) -- CPU time: 31.18 s. Metis reconstruction failed. *}
-- {*sledgehammer [cvc4,timeout=300] suggested following line: *}
-- {*by (smt C14\_B sym\_def trans\_def refl\_def)*} oops
theorem C22_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> r i1 i2 \<and> r i2 i1 \<and> \<not> r i2 i2 \<longrightarrow> \<not> (ser r \<and> sym r \<longrightarrow> (refl r \<and> sym r))" 
 by (metis (full_types) ser_def sym_def refl_def)
lemma C22_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. ser R \<and> sym R \<longrightarrow> (refl R \<and> sym R))"
 by (metis (full_types) ser_def refl_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} () 
          edge node {} (i_2) 
    (i_2) edge [loop above] node {} ();
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* B $>$ M *}

lemma C23_A: "\<forall>R. refl R \<longrightarrow> (refl R \<and> sym R)" nitpick oops
lemma C23_B_ATP_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. refl R \<longrightarrow> (refl R \<and> sym R))"
 oops -- {* All ATPs time out *}
theorem C23_C: "#\<^sup>2 i1 i2  \<and> r i1 i1 \<and> r i1 i2 \<and> \<not> r i2 i1 \<and> r i2 i2  \<longrightarrow> \<not> (refl r \<longrightarrow> (refl r \<and> sym r))" 
 by (metis refl_def sym_def)
lemma C23_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. refl R \<longrightarrow> (refl R \<and> sym R))" by (metis (full_types) sym_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
    \path[->] 
    (i_1) edge [loop above] node {} ()
          edge node {} (i_2)
    (i_2) edge [loop above] node {} ();
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* S5 $>$ S4 *}

lemma C24_A: "\<forall>R. refl R \<and> trans R \<longrightarrow> (refl R \<and> eucl R)"
 nitpick oops

lemma C24_B_ATP_challenge: "#\<^sup>2 i1 i2 \<longrightarrow> \<not> (\<forall>R. refl R \<and> trans R \<longrightarrow> (refl R \<and> eucl R))"
 oops -- {* All ATPs time out *}
theorem C24_C: "#\<^sup>2 i1 i2 \<and> r i1 i1 \<and> r i1 i2 \<and> \<not> r i2 i1 \<and> r i2 i2 \<longrightarrow> \<not> (refl r \<and> trans r \<longrightarrow> (refl r \<and> eucl r))" 
 by (metis (full_types) trans_def refl_def eucl_def)
lemma C24_D: "#\<^sup>1 i1 \<longrightarrow> (\<forall>R. refl R \<and> trans R \<longrightarrow> (refl R \<and> eucl R))" by (metis (full_types) eucl_def)

text {* 
\begin{isbfig}{7em}
\begin{tikzpicture}[shorten >=1pt,node distance=2cm,on grid,auto] 
   \node[state] (i_1)   {$i_1$}; 
   \node[state] (i_2) [right=of i_1] {$i_2$}; 
   \node[state] (i_3) [right=of i_2] {$i_3$}; 
    \path[->] 
    (i_1) edge [loop above] node {} () 
          edge [bend left] node {} (i_2) 
    (i_2) edge [loop above] node {} () 
          edge [bend left] node {} (i_1) 
          edge [bend left] node {} (i_3) 
    (i_3) edge [loop above] node {} () 
          edge [bend left] node {} (i_2);
\end{tikzpicture}
\end{isbfig}
*}

subsubsection {* S5 $>$ B *}
lemma C25_A: "\<forall>R. refl R \<and> sym R \<longrightarrow> (refl R \<and> eucl R)"
 nitpick oops

lemma C25_B_ATP_challenge: "#\<^sup>3 i1 i2 i3 \<longrightarrow> \<not> (\<forall>R. (refl R \<and> sym R) \<longrightarrow> (refl R \<and> eucl R))"
 oops -- {* All ATPs time out *}
theorem C25_C: "#\<^sup>3 i1 i2 i3 \<and> r i1 i1 \<and> r i1 i2 \<and> \<not> r i1 i3 \<and> r i2 i1 \<and> r i2 i2 \<and> r i2 i3 \<and> \<not> r i3 i1 \<and> r i3 i2 \<and> r i3 i3  \<longrightarrow> \<not> ((refl r \<and> sym r) \<longrightarrow> (refl r \<and> eucl r))" 
 by (metis (full_types) eucl_def refl_def sym_def)
lemma C25_D: "#\<^sup>2 i1 i2 \<longrightarrow> (\<forall>R. (refl R \<and> sym R) \<longrightarrow> (refl R \<and> eucl R))"
 by (metis (full_types) refl_def sym_def eucl_def)

section {* Discussion and Future Work. \label{sec:eval} *}

text {* 
The entire Isabelle document can be verified by Isabelle2014 in less than 60s on a semi-modern computer (2.4 GHz Core 2 Duo, 8 GB of memory).
When including all (commented) remote calls to the external ATPs in the calculation the verification time sums up to a few minutes,
which is still very reasonable. 

The improvements in comparison to the first-order based verification of the modal logic cube done
earlier by Rabe et al.~\cite{Rabe}, are: clarity and readability of the problem encodings, methodology,
reliability (our proofs are verifiable in Isabelle/HOL) and, most importantly, automation performance.
For the latter note that the experiments by Rabe et al.~\cite{Rabe} required several days of reasoning 
time in first-order theorem provers. Most importantly, however, their solution relied on an
enormous manual coding effort. However, we want to point again to the more general aims of their work.

Our solution instead requires a small amount of resources in comparison. In fact, as indicated before, 
the entire process (Steps A-D) is schematic, so that it should eventually be possible to fully automate our method.
For this it would be beneficial to have a flexible and accessible
conversion of the countermodels delivered by Nitpick back into Isabelle/HOL input syntax.
In fact, an automated conversion of Nitpick's countermodels into the corresponding @{text "C*_B"} 
and @{text "C*_C"} conjectures would eventually enable a truly automated exploration and verification of 
of the modal logic cube with no or minimal handcoding effort.
Similarly, for the interactive user a 
more intuitive presentation of Nitpick's countermodels would be welcome (perhaps similar to the illustrations we used 
in this paper).


Using the first-order provers E \cite{E}, SPASS \cite{SPASS}, Z3 \cite{Z3} and Vampire \cite{Vampire} proved unsuccessful for 
all @{text "C*_Isabelle_challenge"} problems (unless the right lemmas were given to them). Analyzing the reason for their weakness, as compared to the better performing higher-order automated theorem provers,
remains future work. In contrast, the SMT  solver CVC4 (via Sledgehammer) was quite successful 
and contributed five @{text "C*_Isabelle_challenge"} proofs.


Our work motivates further improvements regarding the integration of LEO-II and Satallax: While these systems
 are able to prove all @{text "*_Isabelle_challenge"} problems their proofs cannot yet be easily replayed or integrated 
in Isabelle/HOL. There have been recent improvements regarding the transformation of proofs from LEO-II and Satallax to 
Isabelle/HOL \cite{sultana14:_higher}, using which all the proofs produced by Satallax and LEO-II in
our work could be checked in Isabelle/HOL,\footnote{The proofs and the evaluation workflow can be downloaded from \url{http://christoph-benzmueller.de/papers/pxtp2015-eval.zip}}
but this process still requires some manual work to adapt the output from the ATPs.

Our work also motivates further improvements in higher-order automated theorem provers. For example, for these
systems it should be possible to also prove the remaining two @{text "*_ATP_challenge"} problems.
Moreover, they needed more than 10 seconds of CPU time in our experiments
for the @{text "*_Isabelle_challenge"} problems; it should be possible to prove these theorems much faster.
 
*}

section {* Conclusion \label{sec:conc} *}

text {*
We have fully verified the modal logic cube in Isabelle/HOL. Our solution is simple, elegant, easy to follow, effective 
and efficient. Proof exchange between systems played a crucial role in our experiments. In particular, we have exploited and combined Nitpick's 
countermodel-finding capabilities with subsequent calls to the higher-order theorem provers LEO-II and Satallax and the SMT solver
CVC4 via Isabelle's Sledgehammer tool. 
Our experiments also point to several improvement opportunities for Isabelle and the higher-order reasoners, in particular, 
regarding interaction and proof exchange.

Related experiments have been
carried out earlier in collaboration with Geoff Sutcliffe. Similar to
and improving on the
work reported in \cite{B12}, these unpublished experiments used the TPTP
THF infrastructure directly. However, in that work we did not achieve
a `trusted verification' in the sense of the work presented in this paper.
Another improvement in this article has been the use of schematic meta-level
working steps (Steps A-D) to systematically convert (counter)models found
by Nitpick into conjectures to be investigated. 

Future work will explore and evaluate similar logic relationships for other non-classical logics, for example, 
conditional logics. Any improvements in the mentioned systems, as motivated above, would be very beneficial
towards this planned work. Moreover, it would be useful to fully automate the schematic, meta-level working steps (Steps A-D) as
applied in our experiments. This would produce a system that would explore
logic relations truly automatically (for example, in conditional logics), analogous to what has been achieved here for the modal logic cube.
*}


text {* \paragraph{Acknowledgements:} We thank Florian Rabe and the anonymous reviewers of this paper 
for their valuable feedback.  *}


(*<*) 
end
(*>*)

