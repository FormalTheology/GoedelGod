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


%----Assuming Theorem 2 (proved before)
thf(thm2,axiom,
    ( mvalid
    @ ( mdia_s5
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).


%----Assuming Theorem 3 (proved before)
thf(thm3,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [Y: mu] :
          ( mimplies @ ( god @ Y ) @ ( essential @ god @ Y ) ) ) )).


%----Definition of necessarily exists
thf(nec_exist_def,definition,
    ( nec_exists
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies @ ( essential @ P @ X )
              @ ( mbox_s5
                @ ( mexists_ind
                  @ ^ [X: mu] :
                      ( P @ X ) ) ) ) ) ) )).

%----Axiom 5 
thf(ax5,axiom,
    ( mvalid @ ( positive @ nec_exists ) )).

   
%----Theorem 4
thf(thm4,conjecture,
    ( mvalid
    @ ( mbox_s5
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).


% Satallax---2.7 : GoedelGod_thm_4.p +++60 secTimeout+++ RESULT: SOT_r4y6s5 - Satallax---2.7 says Theorem - CPU = 3.30 WC = 3.49
% LEO-II---1.6.0 : GoedelGod_thm_4.p +++60 secTimeout+++ RESULT: SOT_WKjZlK - LEO-II---1.6.0 says Theorem - CPU = 6.78 WC = 6.88