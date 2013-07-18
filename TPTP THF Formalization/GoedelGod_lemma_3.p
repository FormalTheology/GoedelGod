%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013

% Informal explanation:
% From
% (axiom_2) A property is positive if and only if its negation is not positive.
% (def_1)   X is God-like if and only if X incorporates all positive properties.
% (def_2)   Property P is an essence of X if and only if P is a property of X and
%           every property Q that X has is strictly implied by P.
% (axiom_4) Positive properties are necessary positive properties.
% we infer
% (lemma_3) If X is a God-like being, then the property of being God-like is an essence of X.

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

%----axiom_2: A property is positive if and only if its negation is not positive.
%----         (Remark: to prove lemma_3 both directions of axiom_2 are required;
%----          if mimplies is used instead of mequiv then Nitrox finds a counterexample;
%----          see also the "Introductory note to *1970", p.401, to "Kurt Goedel (1995),
%----          Ontological Proof, Collected Works: Unpublished Essays & Lectures, Volume III.
%----          pp. 403-404. Oxford University Press.")
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

%----def_2: Property P is an essence of X if and only if P is a property of X and
%----       every property Q that X has is strictly implied by P
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

%----lemma_3: If X is a God-like being, then the property of being God-like is an essence of X.
thf(lemma_3,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mimplies @ ( god @ X ) @ ( essential @ god @ X ) ) ) )).

% Results of an experiment with SystemOnTPTP on July 17, 2013:
% Satallax---2.7 : GoedelGod_lemma_3.p +++60 secTimeout+++ RESULT: SOT_w3T2j7 - Satallax---2.7 says Theorem - CPU = 3.29 WC = 3.99
% LEO-II---1.6.0 : GoedelGod_lemma_3.p +++60 secTimeout+++ RESULT: SOT_usJ6qA - LEO-II---1.6.0 says Theorem - CPU = 17.75 WC = 17.86
