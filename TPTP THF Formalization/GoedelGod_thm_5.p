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


%----Assuming Theorem 4 (proved before)
thf(thm4,axiom,
    ( mvalid
    @ ( mbox_s5
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( god @ X ) ) ) )).
   
   
%----Theorem 5
thf(thm5,conjecture,
    ( mvalid
    @ ( mexists_ind
      @ ^ [X: mu] :
          ( god @ X ) ) )).

% LEO-II---1.6.0 : GoedelGod_thm_5.p +++60 secTimeout+++ RESULT: SOT_r1T6pB - LEO-II---1.6.0 says Theorem - CPU = 0.02 WC = 0.06
% Satallax---2.7 : GoedelGod_thm_5.p +++60 secTimeout+++ RESULT: SOT_wWgbEN - Satallax---2.7 says Theorem - CPU = 0.00 WC = 0.02
