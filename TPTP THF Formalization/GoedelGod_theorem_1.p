%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013

% Informal explanation:
% From
% (def_1)   X is God-like if and only if X incorporates all positive properties.
% (lemma_2) Eventually God exists.
% (lemma_3) If X is a God-like being, then the property of being God-like is an essence of X.
% (def_3)   X necessarily exists if and only if every essence of X is necessarily exemplified.
% (axiom_5) Necessary existence is positive.
% we infer
% (theorem_1) Necessarily God exists.

%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic S5 (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_S5.ax').

%------------------------------------------------------------------------------

thf(god_tp,type,(
    god: mu > $i > $o )).

thf(positive_tp,type,(
    positive: ( mu > $i > $o ) > $i > $o )).

thf(essential_tp,type,(
    essential: ( mu > $i > $o ) > mu > $i > $o )).

thf(nec_exists_tp,type,(
    nec_exists: mu > $i > $o )).   

%----def_1: X is God-like if and only if X incorporates all positive properties.
thf(def_1,definition,
    ( god
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies @ ( positive @ P ) @ ( P @ X ) ) ) ) )).

%----lemma_2 (proved in file GoedelGod_lemma_2.p): Eventually God exists.
thf(lemma_2,axiom,
    ( mvalid
    @ ( mdia_s5
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).

%----lemma_3 (proved in file GoedelGod_lemma_2.p): If X is a God-like being, then the property of
%----        being God-like is an essence of X.
thf(lemma_3,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mimplies @ ( god @ X ) @ ( essential @ god @ X ) ) ) )).

%----def_3: X necessarily exists if and only if every essence of X is necessarily exemplified.
thf(def_3,definition,
    ( nec_exists
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies @ ( essential @ P @ X )
              @ ( mbox_s5
                @ ( mexists_ind
                  @ ^ [Y: mu] :
                      ( P @ Y ) ) ) ) ) ) )).

%----axiom_5: Necessary existence is positive.
thf(axiom_5,axiom,
    ( mvalid @ ( positive @ nec_exists ) )).
 
%----theorem_1: Necessarily God exists.
thf(theorem_1,conjecture,
    ( mvalid
    @ ( mbox_s5
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).

