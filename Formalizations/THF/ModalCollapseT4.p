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

%----D1: A God-like being possesses all positive properties.
thf(defD1,definition,
    ( g
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [Phi: mu > $i > $o] :
              ( mimplies @ ( p @ Phi ) @ ( Phi @ X ) ) ) ) )).

%----Modal Collapse:
thf(prop_tp,type,(prop: $i > $o)).

thf(modalCollapseT4,conjecture,
    ( v @ ( mforall_ind
          @ ^ [X: mu] :
            ( mimplies @ ( g @ X )
                       @ ( mforall_indset
                         @ ^ [Phi: mu > $i > $o] : ( mimplies @ ( Phi @ X ) @ (p @ Phi ) ) ) ) ) )). 