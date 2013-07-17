%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013

% Informal explanation:
% From 
% (axiom_1) Any property strictly implied by a positive property is positive.
% (axiom_2) A property is positive if and only if its negation is not positive.
% we infer
% (lemma_1) Positive properties are eventually exemplified.

%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic S5 (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_S5.ax').
%------------------------------------------------------------------------------

thf(positive_tp,type,(
    positive: ( mu > $i > $o ) > $i > $o )).

%----axiom_1: Any property strictly implied by a positive property is positive.
thf(axiom_1,axiom,
    ( mvalid @
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mforall_indset
              @ ^ [Q: mu > $i > $o] :
                  ( mimplies
                  @ ( mand @ ( positive @ P )
                    @ ( mbox_s5
                      @ ( mforall_ind
                        @ ^ [X: mu] :
                            ( mimplies @ ( P @ X ) @ ( Q @ X ) ) ) ) )
                  @ ( positive @ Q ) ) ) ) )).

%----axiom_2: A property is positive if and only if its negation is not positive.
%             (Remark: only the left to right is actually needed for proving lemma_1)
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

%----lemma_1: Positive properties are eventually exemplified.
thf(lemma1,conjecture,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mimplies @ ( positive @ P )
          @ ( mdia_s5
            @ ( mexists_ind
              @ ^ [X: mu] :
                  ( P @ X ) ) ) ) ) )).

% Results of an experiment with SystemOnTPTP on July 17, 2013:
% LEO-II---1.6.0 : GoedelGod_lemma_1.p +++60 secTimeout+++ RESULT: SOT_JfS0K1 - LEO-II---1.6.0 says Theorem - CPU = 0.06 WC = 0.17
% Satallax---2.7 : GoedelGod_lemma_1.p +++60 secTimeout+++ RESULT: SOT_CLp2TK - Satallax---2.7 says Theorem - CPU = 2.24 WC = 3.49