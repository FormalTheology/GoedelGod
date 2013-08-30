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
include('Quantified_KB.ax').

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



%----D1: A God-like being possesses all positive properties.
thf(defD1,definition,
    ( g
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [Phi: mu > $i > $o] :
              ( mimplies @ ( p @ Phi ) @ ( Phi @ X ) ) ) ) )).



%----A4: Positive properties are necessary positive properties.
thf(axA4,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mimplies @ ( p @ Phi ) @ ( mbox @ ( p @ Phi ) ) ) ) )).

%----T3: Necessarily God exists.
thf(thmT3,axiom,
    ( v
    @ ( mbox
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( g @ X ) ) ) )).

thf(modalCollapseT4,axiom,
    ( v @ ( mforall_ind
          @ ^ [X: mu] :
            ( mimplies @ ( g @ X )
                       @ ( mforall_indset
                         @ ^ [Phi: mu > $i > $o] : ( mimplies @ ( Phi @ X ) @ (p @ Phi ) ) ) ) ) )). 

thf(modalCollapseT7,conjecture,
    ( v @ ( mforall_ind
          @ ^ [X: mu] :
            ( mimplies @ ( g @ X )
                       @ ( mforall_indset
                         @ ^ [Phi: mu > $i > $o] : ( mimplies @ ( Phi @ X ) @ ( mbox @ ( mexists_ind
@ ^ [Y: mu] : ( mand @ ( g @ X ) @ ( Phi @ X ) ) ) ) ) ) ) ) )).

