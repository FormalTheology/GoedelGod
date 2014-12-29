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


