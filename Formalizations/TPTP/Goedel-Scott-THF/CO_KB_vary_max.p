%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013 (update on August 21, 2013)

%----Informal: Scott's version of Goedel's ontological proof
%              Here we are interested in the consistency of the
%              axioms and definitions.


%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic KB.
include('Quantified_KB_varying.ax').

%------------------------------------------------------------------------------

%----constant symbol for positive: p
thf(p_tp,type,(
    p: ( mu > $i > $o ) > $i > $o )).

%----constant symbol for God-like: g
thf(g_tp,type,(
    g: mu > $i > $o )).

%----constant symbol for essence: ess
thf(ess_tp,type,(
    ess: ( mu > $i > $o ) > mu > $i > $o )).

%----constant symbol for necessary existence: ne
thf(ne_tp,type,(
    ne: mu > $i > $o )).

%----A1: Either the property or its negation are positive, but not both.
thf(axA1,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mequiv
          @ ( p
            @ ^ [X: mu] :
                ( mnot @ ( Phi @ X ) ) )
          @ ( mnot @ ( p @ Phi ) ) ) ) )).

%----A2: A property necessarily implied by a positive property is positive.
thf(axA2,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mforall_indset
          @ ^ [Psi: mu > $i > $o] :
              ( mimplies
              @ ( mand @ ( p @ Phi )
                @ ( mbox
                  @ ( mforall_ind
                    @ ^ [X: mu] :
                        ( mimplies @ ( Phi @ X ) @ ( Psi @ X ) ) ) ) )
              @ ( p @ Psi ) ) ) ) )).

%----D1: A God-like being possesses all positive properties.
thf(defD1,definition,
    ( g
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [Phi: mu > $i > $o] :
              ( mimplies @ ( p @ Phi ) @ ( Phi @ X ) ) ) ) )).

%----A3: The property of being God-like is positive.
thf(axA3,axiom,
    ( v @ ( p @ g ) )).

%----A4: Positive properties are necessary positive properties.
thf(axA4,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mimplies @ ( p @ Phi ) @ ( mbox @ ( p @ Phi ) ) ) ) )).

%----D2: An essence of an individual is a property possessed by it and
%----necessarily implying any of its properties
thf(defD2,definition,
    ( ess
    = ( ^ [Phi: mu > $i > $o,X: mu] :
          ( mand @ ( Phi @ X )
          @ ( mforall_indset
            @ ^ [Psi: mu > $i > $o] :
                ( mimplies @ ( Psi @ X )
                @ ( mbox
                  @ ( mforall_ind
                    @ ^ [Y: mu] :
                        ( mimplies @ ( Phi @ Y ) @ ( Psi @ Y ) ) ) ) ) ) ) ) )).

%----D3: Necessary existence of an individual is the necessary 
%----exemplification of all its essences
thf(defD3,definition,
    ( ne
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [Phi: mu > $i > $o] :
              ( mimplies @ ( ess @ Phi @ X )
              @ ( mbox
                @ ( mexists_ind
                  @ ^ [Y: mu] :
                      ( Phi @ Y ) ) ) ) ) ) )).

%----A5: Necessary existence is positive.
thf(axA5,axiom,
    ( v @ ( p @ ne ) )).

