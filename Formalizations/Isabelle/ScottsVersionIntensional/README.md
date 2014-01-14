Dear Reader,

in this file I present intensional embeddings of intensional
quantified modal logics (with constant domain and varying domain
semantics) in Isabelle/HOL.  These intensional embeddings are related
to logics as studyied by Fitting in his book (Types, Tableaus, and
Goedel's God).

The crucial difference to the extensional embedding (as e.g. used in
directory "ScottsVersion") is that the type sigma for lifted formulas
if now extended from sigma := (i => bool) to become sigma := (i => i
=> bool). The idea is that the first argument wold stands for the original
actual world, i.e. the world the evaluation of a formula has started
in.  The second argument is the dynamically changing world in which
the formula is evaluated. This way we can encode both intension and extension
of expressions.

Best regards, 
   Christoph Benzmueller


