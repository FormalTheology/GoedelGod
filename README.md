Computer-Assisted Theoretical Philosophy
========================================

This repository contains 
computer-assisted formalizations 
of ontological proofs. 


Formalizations
--------------

The [formalizations](https://github.com/FormalTheology/GoedelGod/tree/master/Formalizations) 
use three kinds of tools:

* [Coq](http://coq.inria.fr/)

* [Isabelle](https://isabelle.in.tum.de/)

* Automated Theorem Provers compatible with the 
[TPTP THF](http://www.cs.miami.edu/~tptp/TPTP/Proposals/THF.html) 
format (e.g. 
[LEO-II](http://page.mi.fu-berlin.de/cbenzmueller/leo/) and 
[Satallax](https://mathgate.info/cebrown/satallax/)).

In order to verify the Coq and Isabelle proofs, 
you must install and use these tools. 
To re-execute the TPTP THF files, 
you may either install and use any of the automated provers 
or use our [remote call script](https://github.com/FormalTheology/GoedelGod/blob/master/Formalizations/THF/call_tptp.sh), 
which will call provers installed remotely in a server in Miami. 
The [ECAI script](https://github.com/FormalTheology/GoedelGod/blob/master/Formalizations/THF/Run_ECAI2014_Experiments.sh) 
executes our remote call script on many of the available files.


Scientific Publications
-----------------------

Have a look on our [Papers](https://github.com/FormalTheology/GoedelGod/tree/master/Papers/). 
There are short invited abstracts as well as full-length peer-
reviewed scientific publications describing and explaining
the formalizations. 
If you would like to cite these papers, you may use the bibligraphical
information available in our [bibtex file](https://github.com/FormalTheology/GoedelGod/tree/master/Papers/Papers.bib).


Frequently Asked Questions
--------------------------


** What do these proofs prove exactly? **

In formal logic, every proof is a rigorous derivation of a theorem
from a set of assumed axioms, using strict and mathematically well-
defined inference rules. In any theory (independently of whether it
is about physical objects, such as atoms or planets, or about
metaphysical notions, such as gods), the axioms are always assumed
without proof. Therefore, they are open for critical debate (including
empirical considerations). What formal logic and the automated
reasoning systems based on it guarantee is that if you accept the
axioms and the inference rules, then you can safely accept the proven
theorems. Nothing else.

Logic is at the very heart of the scientific method, which
consists of formulating theories (i.e. sets of axioms), using them for
obtaining predictions (i.e. theorems) and revising them when
necessary. 


** Is the "god" of ontological proofs the same "god" of common religions? **


** Isn't it impossible to prove god's existence by pure reason? **


** How is this useful? **

These proofs require special kinds of formal logics known as *higher-order modal logics*. They are called *modal* because they allow reasoning with modal adverbs such as *necessarily* and *possibly*. And they are called *higher-order* because they allow reasoning not only about objects, but also about properties of objects.

Before we started working on these proofs, there was no automated reasoning technology capable of dealing with such logics. Therefore, the formalisation of these proofs seemed like a challenging goal to motivate the development of this technology, which is potentially useful outside philosophy as well.

Moreover, we hope that the media attention gathered by this work will bring a higher level of awareness of formal logic to the general public. 

