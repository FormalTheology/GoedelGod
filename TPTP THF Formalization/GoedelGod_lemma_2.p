%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July,16 2013


% Informal explanation:
% From
% (axiom_2) A property is positive if and only if its negation is not positive.
% (lemma_1) Positive properties are eventually exemplified.
% (def_1)   X is God-like if and only if X incorporates all positive properties.
% (axiom_3) The property of being God-like is positive.
% we infer
% (lemma_2) Eventually God exists.

%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic S5 (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_S5.ax').

%------------------------------------------------------------------------------

thf(god_tp,type,(
    god: mu > $i > $o )).

thf(positive_tp,type,(
    positive: ( mu > $i > $o ) > $i > $o )).

%----axiom_2: A property is positive if and only if its negation is not positive.
%             (Remark: only the left to right is actually needed for proving lemma_2)
thf(axiom2,axiom,
    ( mvalid @
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mequiv
              @ ( positive @ P )                
              @ ( mnot
                @ ( positive 
                  @ ^ [W: mu] :
                    ( mnot @ ( P @ W ) ) ) ) ) ) )).

%----lemma_1 (proved in file GoedelGod_lemma_1.p)
% Positive properties are eventually exemplified.
thf(lemma_1,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mimplies @ ( positive @ P )
          @ ( mdia_s5
            @ ( mexists_ind
              @ ^ [X: mu] :
                  ( P @ X ) ) ) ) ) )).

%----def_1: X is God-like if and only if X incorporates all positive properties.
thf(def_1,definition,
    ( god
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies @ ( positive @ P ) @ ( P @ X ) ) ) ) )).

%----axiom_3: The property of being God-like is positive.
thf(axiom_3,axiom,
    ( mvalid @ ( positive @ god ) )).

%----lemma_2: Eventually God exists.
thf(lemma_2,conjecture,
    ( mvalid
    @ ( mdia_s5
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).

% Results of an experiment with SystemOnTPTP on July 17, 2013:
% LEO-II---1.6.0 : GoedelGod_lemma_2.p +++60 secTimeout+++ RESULT: SOT_fVK1wH - LEO-II---1.6.0 says Theorem - CPU = 0.07 WC = 0.10
% Satallax---2.7 : GoedelGod_lemma_2.p +++60 secTimeout+++ RESULT: SOT_njgGdM - Satallax---2.7 says Theorem - CPU = 0.39 WC = 0.54

