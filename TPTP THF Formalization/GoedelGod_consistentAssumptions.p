%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July 2013

% Informal explanation:
% We prove consistency of all basic assumptions as used in our proofs for GoedelGod:
% (axiom_1) Any property strictly implied by a positive property is positive.
% (axiom_2) A property is positive if and only if its negation is not positive.
% (def_1)   X is God-like if and only if X incorporates all positive properties.
% (axiom_3) The property of being God-like is positive.
% (def_2)   Property P is an essence of X if and only if P is a property of X and
%           every property Q that X has is strictly implied by P.
% (axiom_4) Positive properties are necessary positive properties.
% (def_3)   X necessarily exists if and only if every essence of X is necessarily exemplified.
% (axiom_5) Necessary existence is positive.

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
                  @ ( positive @ Q ) ) ) ) ) ).

%----axiom_2: A property is positive if and only if its negation is not positive.
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

%----def_2: Property P is an essence of X if and only if P is a property of X and
%           every property Q that X has is strictly implied by P.
thf(def_2,definition,
    ( essential
    = ( ^ [P: mu > $i > $o,X: mu] :
          ( mand @ ( P @ X )
          @ ( mforall_indset
            @ ^ [Q: mu > $i > $o] :
                ( mimplies @ ( Q @ X )
                @ ( mbox_s5
                  @ ( mforall_ind
                    @ ^ [Y: mu] :
                        ( mimplies @ ( P @ Y ) @ ( Q @ Y ) ) ) ) ) ) ) ) )).

%----axiom_4: Positive properties are necessary positive properties.
thf(axiom_4,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mimplies @ ( positive @ P ) @ ( mbox_s5 @ ( positive @ P ) ) ) ) )).

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

% Results of an experiment with SystemOnTPTP on July 17, 2013:
% Nitrox---2013 : GoedelGod_consistentAssumptions.p +++60 secTimeout+++ RESULT: SOT_xKMpmb - Nitrox---2013 says Satisfiable - CPU = 5.88 WC = 9.77

% Nitrox refers to Nitpick (from Jasmin Blanchette)
% Here is the finite model it generates
% SZS status Satisfiable
% SZS output start FiniteModel
% Nitpick found a model for card TPTP_Interpret.ind = 1 and card bnd_mu = 1:
%
%  Constants:
%    bnd_positive =
%      (%x. _)
%      ((%x. _)(b1 := (%x. _)(i1 := True)) := (%x. _)(i1 := True),
%       (%x. _)(b1 := (%x. _)(i1 := False)) := (%x. _)(i1 := False))
%    bnd_rel_s5 = (%x. _)(i1 := (%x. _)(i1 := True))
% SZS output end FiniteModel
% Total time: 4.66 s.
%
% END OF SYSTEM OUTPUT
% RESULT: SOT_kBmYMI - Nitrox---2013 says Satisfiable - CPU = 7.44 WC = 7.26 
% OUTPUT: SOT_kBmYMI - Nitrox---2013 says FiniteModel - CPU = 7.44 WC = 7.27 