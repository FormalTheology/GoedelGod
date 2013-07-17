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


%----Definition of essential   
thf(essential_def,definition,
    ( essential
    = ( ^ [P: mu > $i > $o,X: mu] :
          ( mand @ ( P @ X )
          @ ( mforall_indset
            @ ^ [Q: mu > $i > $o] :
                ( mimplies @ ( Q @ X )
                @ ( mbox_s5
                  @ ( mforall_ind
                    @ ^ [Z: mu] :
                        ( mimplies @ ( P @ Z ) @ ( Q @ Z ) ) ) ) ) ) ) ) )).

%----Axiom 4 
thf(ax4,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mimplies @ ( positive @ P ) @ ( mbox_s5 @ ( positive @ P ) ) ) ) )).


%----Theorem 3 
thf(thm3,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [Y: mu] :
          ( mimplies @ ( god @ Y ) @ ( essential @ god @ Y ) ) ) )).


% Satallax---2.7 : GoedelGod_thm_3.p +++60 secTimeout+++ RESULT: SOT_OKAAwp - Satallax---2.7 says Theorem - CPU = 2.85 WC = 4.16
% LEO-II---1.6.0 : GoedelGod_thm_3.p +++60 secTimeout+++ RESULT: SOT_yf1H29 - LEO-II---1.6.0 says Theorem - CPU = 18.10 WC = 18.87