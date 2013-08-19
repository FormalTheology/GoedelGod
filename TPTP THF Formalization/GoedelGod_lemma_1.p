%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013 (update on August 10, 2013)

% Informal explanation:
% From 
% (axiom_1)  Any property strictly implied by a positive property is positive.
% (axiom_2a) When a property is positive then its negation is not positive.
% we infer
% (lemma_1) Positive properties are eventually exemplified.

%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic KB (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_KB.ax').
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
                    @ ( mbox
                      @ ( mforall_ind
                        @ ^ [X: mu] :
                            ( mimplies @ ( P @ X ) @ ( Q @ X ) ) ) ) )
                  @ ( positive @ Q ) ) ) ) )).

%----axiom_2a: When a property is positive then its negation is not positive.
%----(Remark: only the left to right is actually needed for proving lemma_1)
thf(axiom2a,axiom,
    ( mvalid @
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies
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
          @ ( mdia
            @ ( mexists_ind
              @ ^ [X: mu] :
                  ( P @ X ) ) ) ) ) )).

