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
                    @ ( mbox
                      @ ( mforall_ind
                        @ ^ [X: mu] :
                            ( mimplies @ ( P @ X ) @ ( Q @ X ) ) ) ) )
                  @ ( positive @ Q ) ) ) ) ) ).

%----axiom_2: Either the property or its negation are positive, but not both.
thf(axiom_2,axiom,
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

%----axiom_3: The property of being God-like is positive.
thf(axiom_3,axiom,
    ( mvalid @ ( positive @ god ) )).

%----def_2: P is the essence of X if and only if X has P and this property is 
%----necessarily minimal.
thf(def_2,definition,
    ( essential
    = ( ^ [P: mu > $i > $o,X: mu] :
            ( mforall_indset
            @ ^ [Q: mu > $i > $o] :
                ( mimplies @ ( Q @ X )
                @ ( mbox
                  @ ( mforall_ind
                    @ ^ [Y: mu] :
                        ( mimplies @ ( P @ Y ) @ ( Q @ Y ) ) ) ) ) ) ) )).

%----axiom_4: Positive properties are necessary positive properties.
thf(axiom_4,axiom,
    ( mvalid
    @ ( mforall_indset
      @ ^ [P: mu > $i > $o] :
          ( mimplies @ ( positive @ P ) @ ( mbox @ ( positive @ P ) ) ) ) )).

%----def_3: X necessarily exists if and only if every essence of X is necessarily
%----exemplified.
thf(def_3,definition,
    ( nec_exists
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [P: mu > $i > $o] :
              ( mimplies @ ( essential @ P @ X )
              @ ( mbox
                @ ( mexists_ind
                  @ ^ [Y: mu] :
                      ( P @ Y ) ) ) ) ) ) )).

%----axiom_5: Necessary existence is positive.
thf(axiom_5,axiom,
    ( mvalid @ ( positive @ nec_exists ) )).

