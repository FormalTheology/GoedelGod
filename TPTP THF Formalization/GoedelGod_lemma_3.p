%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013 (update on August 10, 2013)

%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic KB (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_KB.ax').

%------------------------------------------------------------------------------

thf(god_tp,type,(
    god: mu > $i > $o )).

thf(positive_tp,type,(
    positive: ( mu > $i > $o ) > $i > $o )).

thf(essential_tp,type,(
    essential: ( mu > $i > $o ) > mu > $i > $o )).

%----axiom_2: Either the property or its negation are positive, but not both.
%----         (Remark: to prove lemma_3 both directions of axiom_2 are required;
%----          see also the "Introductory note to *1970", p.401, to "Kurt Goedel (1995).
%----          Ontological Proof, Collected Works: Unpublished Essays & Lectures, Volume III.
%----          pp. 403-404. Oxford University Press.")
thf(axiom2,axiom,
    ( mvalid @
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mequiv
              @ ( positive @ ^ [X: mu] : ( mnot @ ( P @ X ) ) )               
              @ ( mnot @ ( positive @ P ) ) ) ) )).


%----def_1: X is God-like if and only if X incorporates all positive properties.
thf(def_1,definition,
    ( god
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies @ ( positive @ P ) @ ( P @ X ) ) ) ) )).

%----def_2: P is the essence of X if and only if X has P and this property is 
%----necessarily minimal.
thf(def_2,definition,
    ( essential
    = ( ^ [P: mu > $i > $o,X: mu] :
          ( mand @ ( P @ X )
          @ ( mforall_indset
            @ ^ [Q: mu > $i > $o] :
                ( mimplies @ ( Q @ X )
                @ ( mbox
                  @ ( mforall_ind
                    @ ^ [Y: mu] :
                        ( mimplies @ ( P @ Y ) @ ( Q @ Y ) ) ) ) ) ) ) ) )).

%----axiom_4: Positive properties are necessarily positive properties.
thf(axiom_4,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mimplies @ ( positive @ P ) @ ( mbox @ ( positive @ P ) ) ) ) )).

%----lemma_3: If X is a God-like being, then the property of being God-like is an essence of X.
thf(lemma_3,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mimplies @ ( god @ X ) @ ( essential @ god @ X ) ) ) )).
