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

%----Definition of god
thf(god_def,definition,
    ( god
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies @ ( positive @ P ) @ ( P @ X ) ) ) ) )).

%----Assuming Theorem 1 (proved before) 
thf(thm1,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mimplies @ ( positive @ P )
          @ ( mdia_s5
            @ ( mexists_ind
              @ ^ [X: mu] :
                  ( P @ X ) ) ) ) ) )).

%----Axiom 2 
thf(ax2,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mequiv
          @ ( positive
            @ ^ [W: mu] :
                ( mnot @ ( P @ W ) ) )
          @ ( mnot @ ( positive @ P ) ) ) ) )).              

%----Axiom 3
thf(ax3,axiom,
    ( mvalid @ ( positive @ god ) )).

%----Theorem 2
thf(thm2,conjecture,
    ( mvalid
    @ ( mdia_s5
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).

% LEO-II---1.6.0 : GoedelGod_thm_2.p +++30 secTimeout+++ RESULT: SOT_JLEiVy - LEO-II---1.6.0 says Theorem - CPU = 0.04 WC = 0.19
% Satallax---2.7 : GoedelGod_thm_2.p +++30 secTimeout+++ RESULT: SOT_jUPVK8 - Satallax---2.7 says Theorem - CPU = 2.05 WC = 3.44