## Short Summmary

I have formalized and automated several philosophical arguments using [Isabelle](https://isabelle.in.tum.de/). This work stands in the tradition of Computational Philosophy pioneered by Oppenheimer, Zalta, Benzmüller, Woltzenlogel-Paleo and others.
The resulting Isabelle files can further be seen as a guideline for the efficient treatment of similar arguments in philosophy and related areas.

The philosophical Arguments include the computational verification and further exploration of already formal arguments by Jan Salamucha, Charles Jarret, Joel Friedman and Blum & Malinovich as well as translating natural language arguments into formal logic. These natural language arguments are the [Simulation Argument](https://www.simulation-argument.com/) by Nick Bostrom that deals with the possibility that we are living our lives in a simulated reality and arguments for god's existence by Spinoza and Leibniz.

## Technical Summary

During this project a number of philosophical arguments have been translated into formal logic, implemented in [Isabelle](https://isabelle.in.tum.de/), automated, and computationally verified. In the following paragraphs difficulties as well as opportunities for further work will be presented for each argument.

### Leibniz' first cosmological argument

Leibniz' first cosmological argument has been translated into formal logic and implemented in Isabelle. Some parts of Leibniz' argument are structured in a way a formal proof cannot easily mimic. The formalization tries to stay faithful to the overall argument while changing these parts.
For the argument to succeed a couple of extra premises were introduced that Leibniz could have, should have, and hopefully would have accepted. It was not proven that the set of extra premises is minimal. This could be investigated further.
There are also minor changes to the original premises to preserve the spirit of the argument (i.e. an existential guard and a biconditional instead of an implication are used). It may be interesting to see whether the argument changes significantly if these changes are left out. For further details see [this file](https://gitlab.com/aossie/ComputationalPhilosophy/blob/master/Formalizations/Isabelle/Leibniz-Cosmological/LeibnizFurther.thy).


### Salamucha's formalization of Thomas Aquinas' Ex Motu argument

In the collection [Knowledge and Faith](https://books.google.com.au/books?id=ptm1xOmPl3AC&printsec=frontcover&source=gbs_ge_summary_r&cad=0#v=onepage&q&f=false) Salamucha presents a translation of Thomas Aquinas' Ex Motu argument into formal logic. This translation has been implemented in Isabelle and computationally verified. As far as possible with the computational resources at hand consistency and (potential) redundancy of the premises have been checked computationally.
Besides running the Isabelle file with faster computers, very little remains to be done. In a footnote Salamucha mentions that certain proofs work with different notions of equality. This has not been checked, since it adds very little to the structure or content of the argument. There are also a couple of premises that are stated in natural language. Only those that are needed for the cosmological argument to succeed have been translated into formal logic. It may or may not be fruitful to try to translate those parts that Salamucha skipped.

### Nick Bostrom's Simulation Argument

In Nick Bostrom's [Simulation Argument](https://www.simulation-argument.com/) Bostrom argues that either we (as a civilization) are very likely to go extinct before reaching what he calls a "posthuman stage" or such a posthuman society is very likely not running simulations of their ancestral history or we are very likely living in a simulation.

Bostrom's argument is elliptical and may very well not be valid (for some of these concerns see the linked papers on the website as well as the Isabelle file for Bostrom). In its original formalization even Bostrom admits that there is a non-sequitur, for which Bostrom and Kulczycki submitted two possible [patches](http://www.simulation-argument.com/patch.pdf) in form of additional premises.

The simulation argument has been translated to higher order logic where possible. Collections of individuals in civilizations or simulations are modeled with sets. There might be other ways to encode the argument. The set heavy formalization has the advantage of being highly modular so that different sets of premises can easily be implemented and their respective advantages and disadvantages computationally tested.
Only the first patch has been implemented because Bostrom & Kulczycki give a clear outline of how they think the proof should be carried out in their paper.
The second patch uses different (additional) premises to reach the same conclusion. It should not be all that difficult to implement the second patch on top of the already existing set theoretic framework.

It is also of interest to see if there is a better version of this argument, both in formal logic and natural language, and how exploring the first in Isabelle impacts the latter.
Lastly, it is not clear, what the right version of what Bostrom calls the "Bland Indifference Principle" is. The principle is roughly: Given that you know that there are x percent of A in a given sample that includes you and you have no other information on the likelyhood of you being an A, your subjective probability that you are an A should equal x percent.
There are issues with the correct interpretation of this principle (see for example [here](http://www.simulation-argument.com/weatherson.pdf) or the comments in the Isabelle file).
It is an open question whether there is a good interpretation that makes the (valid) formalization in Isabelle a sound one.



### The first Chapter of Spinoza's Ethics

As far as we know there are three existing formalizations of (parts) of the first Chapter of Spinoza's Ethics. These formalizations have been automated in Isabelle although the natural deduction steps (where there are any) have not been reproduced step by step. Their consistency has been checked. For further investigation these could be implemented and it could be checked whether the axioms are redundant (a first finding: no formalization needs A6).

Since none of the existing formalizations are both complete and remain faithful to the original Spinoza text a new formalization that relies heavily on the [existing formalization](https://link.springer.com/article/10.1007%2FBF00869440) by Charles Jarret has been started. As of the time of this writing the formalization is not yet complete.
It may be interesting to try to reproduce the proofs that Spinoza gives for his various propositions, although one might soon stumble upon the limitations of working in modal contexts in Isabelle as well as Spinoza's less than rigorous proofs.


## Links

### Gitlab Page

You can find the project [here](https://gitlab.com/aossie/ComputationalPhilosophy/)

### GSoC2017 tag

TODO

### List of Merge Requests

#### Closed Merge Requests

[MR19: Possible inconsistency in formalized version of Leibniz Argument ](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/19)

Shows that given a formalization that relies heavily on sets Leibniz Cosmological Argument becomes inconsistent, given a certain plausible suppressed premises.

[MR21: Add translation manual for Salamuchas' notation](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/21)

In his formalization of Thomas Aquinas' cosmological argument Salamucha is using unusual logical notation. This MR provides a translation manual.

[MR23:  Add Scans for Salamucha](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/23)

Salamucha's book is not available in all libraries. This MR adds a few pages to the repository.


[MR22:  Formalization Salamucha](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/22)

Automates Salamucha's formalization and fills in gaps in the formal argument where Salamucha only has natural language. Investigates whether the axiom set is consistent and if there are redundant axioms.

[MR25:  Make Salamucha prettier](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/25)
Splits the Salamucha automation in a reconstruction of the original argument and a file for further investigation. Also makes sure that the style used conforms to other recent formalizations in the Project.

[MR:30  Be even more explicit about what goes wrong without explicit types](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/30)
For a certain proof an explicit type declaration was needed for it to succeed. This is perplexing, as it should not be necessary. This MR adds a more clearly worded paragraph to the Isabelle file

[MR:32  Add Christph's Nitpick results ](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/32)

Adds results from the countermodel finder Nitpick run from a different computer.

[MR 29:  Put Leibniz inconsistency in new folder](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/29)

This is an unfortunately named MR. It started as a workaround for a bug encountered on Gitlab where we couldn't commit changed to an existing file. It (d)evolved into a complete overhaul of the formalization of Leibniz' Cosmological Argument (see [MR19](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/19)). The new formalization tries to eliminate all notions foreign to the historical context of Leibniz' argument (e.g. sets) other than the formal language the formalization is in itself.

[MR 33: Rename Files](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/33)

Renames the files used in the formalization of Leibniz' Cosmological argument.

[MR 34:  Give extra axioms new names, fix infix notation, fix typos, misc. notational improvements](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/34)

Fixes typos and provides other minor improvements to the aforementioned formalization of Leibniz' Cosmological Argument.


#### Open Merge Requests

[MR 26: Formalization of Bostrom's appendix / "first patch simulation argument"](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/26)

Implements a formalization and automation of Nick Bostrom's [Simulation Argument](https://www.simulation-argument.com/). The formalization models simulations and real civilizations as sets. It lays bare the problematic pieces in the original natural language argument.

[MR 31: Implement the three known formalizations of the first Part of Spinoza's Ethics](https://gitlab.com/aossie/ComputationalPhilosophy/merge_requests/31)

There are (as far as we know) three (partial) formalizations of the first Chapter of Spinoza's ethics.
In this MR these are implemented in Isabelle and checked for things like consistency.
At this point in time still work in progress: Find a better formalization for the first Chapter of Spinoza's ethics that avoids the shortcomings of these existing formalizations
