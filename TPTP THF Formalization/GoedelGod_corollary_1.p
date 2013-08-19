%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013

% Informal explanation:
% From
% (theorem_1) Necessarily God exists.
% we infer
% (corollary_1) God exists.

%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic KB (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_KB.ax').

%------------------------------------------------------------------------------

thf(god_tp,type,(
    god: mu > $i > $o )).

%----axiom reflexivity: we need to assume this to obtain the corollary
%----thus, we here need logic MB
thf(reflexivity,axiom,
    ( ![X:$i]: ( rel @ X @ X ) )).


%----theorem_1: Necessarily God exists.
thf(theorem_1,axiom,
    ( mvalid
    @ ( mbox
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).
   
%----corollary_1: God exists.
thf(corollary_1,conjecture,
    ( mvalid
    @ ( mexists_ind
      @ ^ [X: mu] :
          ( god @ X ) ) )).




