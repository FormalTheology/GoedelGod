%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013 (update on August 21, 2013)

%----Informal: Scott's version of Goedel's ontological proof

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

thf(thmFG_con,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mforall_ind
          @ ^ [X: mu] :
              ( mimplies @ ( g @ X ) @ ( mimplies @ ( mnot @ ( p @ Phi ) ) @ ( mnot @ ( Phi @ X ) ) ) ) ) ) )).

thf(mequals_type,type,(
    mequals: mu > mu > $i > $o )).

thf(mequals,definition,
    ( mequals
    = ( ^ [X: mu,Y: mu,W: $i] : ( X = Y ) ) )).

thf(thmMT_con,conjecture,
    ( v
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mimplies @ ( g @ X ) @ ( mimplies @ ( g @ Y ) @ ( mequals @ X @ Y ) ) ) ) ) )).