%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July 2013


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

%----Axiom 1 (only needed for showing Theorem 1)
thf(ax1,axiom,
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
                  @ ( positive @ Q ) ) ) ) ) ).

%----Axiom 2 (only needed for showing Theorem 1)
thf(ax2,axiom,
    ( mvalid @
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mequiv
              @ ( positive
                @ ^ [W: mu] :
                    ( mnot @ ( P @ W ) ) )
              @ ( mnot @ ( positive @ P ) ) ) ) ) ).


%----Theorem 1
thf(thm1,conjecture,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mimplies @ ( positive @ P )
          @ ( mdia_s5
            @ ( mexists_ind
              @ ^ [X: mu] :
                  ( P @ X ) ) ) ) ) )).

% LEO-II---1.6.0 : GoedelGod_thm_1.p +++30 secTimeout+++ RESULT: SOT_Kss3oR - LEO-II---1.6.0 says Theorem - CPU = 0.08 WC = 0.50
% Satallax---2.7 : GoedelGod_thm_1.p +++30 secTimeout+++ RESULT: SOT_0Ct29C - Satallax---2.7 says Theorem - CPU = 0.70 WC = 3.81