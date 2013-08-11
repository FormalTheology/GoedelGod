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
%----Axioms for Quantified Modal Logic S5 (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_S5.ax').

%------------------------------------------------------------------------------

thf(god_tp,type,(
    god: mu > $i > $o )).

%----theorem_1: Necessarily God exists.
thf(theorem_1,axiom,
    ( mvalid
    @ ( mbox_s5
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).
   
%----corollary_1: God exists.
thf(corollary_1,conjecture,
    ( mvalid
    @ ( mexists_ind
      @ ^ [X: mu] :
          ( god @ X ) ) )).




