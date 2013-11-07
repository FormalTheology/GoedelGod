Goedel's Ontological Proof in TPTP THF
======================================

%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013 (update on November 7, 2013)

We present a formalization and (partial) automation of Goedel's
ontological argument in quantified modal logic KB (QML KB). QML KB is in 
turn modeled as a fragment of Church's simple type theory (HOL). Thus, the
formalization is essentially a formalization in HOL. For our encoding
of HOL formulas we employ the TPTP THF0 syntax. 

For more information on this syntax we refer to:
-- Automated Reasoning in Higher-Order Logic using the TPTP THF 
   Infrastructure (Geoff Sutcliffe, Christoph Benzmüller), In Journal 
   of Formalized Reasoning, volume 3, number 1, pp. 1-27, 2010.
   http://jfr.unibo.it/article/view/1710/1179

The employed embedding of QML in HOL is adapting the ideas as presented in: 
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

Note that our QML formalization employs quantification over individuals and 
quantification over sets of individuals.


Dana Scott's version of Goedel's proof employs the following axioms (A), 
definitions (D), corollaries (C) and theorems (T), and it proceeds in the 
following order:

A1 Either a property or its negation is positive, but not both
A2 A property necessarily implied by a positive property is positive
T1 Positive properties are possibly exemplified: 
D1 A God-like being possesses all positive properties
A3 The property of being God-like is positive
C  Possibly, God exists
A4 Positive properties are necessarily positive
D2 An essence of an individual is a property possessed by it and 
   necessarily implying any of its properties
T2 Being God-like is an essence of any God-like being
D3 Necessary existence of an individual is the necessary exemplification 
   of all its essences 
A5 Necessary existence is a positive property. 
T3 Necessarily, God exists.


Automated theorem provers and model finders for HOL (LEO-II, Satallax and 
Nitpick) are employed to:
- show the consistency of the axioms and definitions employed
- to automate the ontological argument in 4 single steps

Moreover, these systems have been used to obtain the following results:
- The basic modal logic K is sufficient for proving T1, C and T2. 
- Modal logic S5 is not needed for proving T3; the logic KB is sufficient. 
- Without the first conjunct in D2 the set of axioms and definitions 
  would be inconsistent (see also below). 
- For proving theorem T1, only the left to right direction of axiom A1 is 
  needed. However, the backward direction of A1 is required for proving T2.


Informal explanation of the experiments on Goedel's arguments (and
results obtained on standard PCs):

*** File Consistency.p ***

The consistency of the set of axioms can be shown by Nitrox (Nitpick).

Consistency.p ++++++ Nitrox---2013 says Satisfiable - CPU = 7.23 WC = 7.18
Consistency.p ++++++ LEO-II---1.6.0 says Timeout - CPU = 90.06 WC = 90.11
Consistency.p ++++++ Satallax---2.7 says Timeout - CPU = 90.07 WC = 90.51


*** File T1.p (A1, A2 |- T1) ***

This can be proved by LEO-II and Satallax; just apply the provers to
T1.p Remark: Only the left to right direction of A1 is required. Logic
K is sufficient.
  
T1.p ++++++ Satallax---2.7 says Theorem - CPU = 0.00 WC = 0.03
T1.p ++++++ LEO-II---1.6.0 says Theorem - CPU = 0.05 WC = 0.08
T1.p ++++++ Nitrox---2013 says Timeout - CPU = 90.10 WC = 75.88


*** File C.p: (T1, D1, A3 |- C) ***

This can be proved by LEO-II and Satallax; D1 seems not required to
obtain C; in a previous version A2 was also assumed; A2 is not
needed. Logic K is sufficient.

C.p ++++++ LEO-II---1.6.0 says Theorem - CPU = 0.02 WC = 0.05
C.p ++++++ Satallax---2.7 says Theorem - CPU = 0.00 WC = 0.11
C.p ++++++ Nitrox---2013 says Timeout - CPU = 90.07 WC = 65.78


*** File T2.p (A1, D1, D2, A4 |- T2) ***

This can be proved by LEO-II and Satallax; both directions of A1 are
required, otherwise Nitrox (Nitpick) finds a counterexample. Logic K
is sufficient.

T2.p ++++++ Satallax---2.7 says Theorem - CPU = 0.00 WC = 0.12
T2.p ++++++ LEO-II---1.6.0 says Theorem - CPU = 24.22 WC = 24.45
T2.p ++++++ Nitrox---2013 says Timeout - CPU = 90.04 WC = 60.28


*** File T3.p (D1, C, T2, D3, A5 |- T3) ***

This can be proved by LEO-II and Satallax. Logic KB is sufficient. In
Logic K Nitrox finds a counterexample.

T3.p ++++++ LEO-II---1.6.0 says Theorem - CPU = 0.04 WC = 0.07
T3.p ++++++ Satallax---2.7 says Theorem - CPU = 0.00 WC = 0.16
T3.p ++++++  Nitrox---2013 says Unknown - CPU = 3.14 WC = 3.39


In the experiments above the provers were run with a 90 seconds
timeout via Geoff Sutcliffe's SystemOnTPTP interface on standard PCs;
big thanks to Geoff!

We are currently testing whether T3 can eventually be proved directly
from the axioms and definitions in one step; see file T3oneStep.p

Moreover, we have checked the above theorems wrt to varying domain
semantics for quantification over individuals. The respective problem
formulations ar give in files: T1_varying.p C_varying.p T2_varying.p
T3_varying.p; these in turn include the modified files
Quantified_KB_varying.ax resp. Quantified_K_varying.ax. The
experiments confirm is that all theorems remain valid.


Some further results:
=====================

Modal Collapse: Modal collapse (p => []p) is a major critic on Goedel's 
proof. Our experiments confirm that the modal collapse holds. The problem 
encoding is given in file ModalCollapse.p

Inconsistency of Goedel's original axioms: In Goedel's original
definition of essence the first conjunct (Phi(X)) is missing. Without
this first conjunct the theory becomes inconsistent. The relevant
axioms and definitions are A1a, A2, A5, D2, and D3. The problem is
encoded in files InconsistencyWithoutFirstConjunctinD2.p and
InconsistencyWithoutFirstConjunctinD2_minimized.p. The output of the
provers can be found in the files
InconsistencyWithoutFirstConjunctinD2_minimized.*.txt


Best regards,
   Christoph Benzmueller and Bruno Woltzenlogel-Paleo


