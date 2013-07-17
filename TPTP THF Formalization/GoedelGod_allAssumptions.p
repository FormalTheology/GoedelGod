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


%----Definition of god
thf(god_def,definition,
    ( god
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies @ ( positive @ P ) @ ( P @ X ) ) ) ) )).

%----Axiom 3
thf(ax3,axiom,
    ( mvalid @ ( positive @ god ) )).

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

% Nitrox---2013 : GoedelGod_allAssumptions.p +++60 secTimeout+++ RESULT: SOT_10ert5 - Nitrox---2013 says Satisfiable - CPU = 6.53 WC = 9.63