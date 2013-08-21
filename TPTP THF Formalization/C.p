%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013 (update on August 21, 2013)

% Informal: Scott's version of Goedel's ontological proof.
%           Here we prove statement C.

%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic K. 
include('Quantified_KB.ax').

%------------------------------------------------------------------------------

%----constant symbol for positive: p
thf(p_tp,type,(
    p: ( mu > $i > $o ) > $i > $o )).

%----constant symbol for God-like: g
thf(g_tp,type,(
    g: mu > $i > $o )).

%----T1: Positive properties are possibly exemplified. (Proved in T1.p)
thf(thmT1,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mimplies @ ( p @ Phi )
          @ ( mdia
            @ ( mexists_ind
              @ ^ [X: mu] :
                  ( Phi @ X ) ) ) ) ) )).

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

%----C: Possibly, God exists.
thf(corC,conjecture,
    ( v
    @ ( mdia
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( g @ X ) ) ) )).


