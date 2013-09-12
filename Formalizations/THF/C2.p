%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013 (update on September 12, 2013)

% Informal: Here we show that a corollary C2 ("God exists"),
%           which is known to follow trivially from theorem T3
%           by using the modal logic axiom T, 
%           can be proven directly (though not as trivially)
%           from corollary C, theorem T2, axiom A5
%           and the modal logic axiom B. 
%           In other words, theorem T3 and, more importantly,
%           axiom T are not needed! Theorem T3 could then be 
%           derived trivially from C2 by a single application of
%           necessitation.
%           Note that C2 is stated neither by Gödel nor by Scott.
%           This result was first achieved by Annika Siders on 10/09/2013 while
%           she improved the derivation of T3 in our natural deduction formalization.


%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic KB.
include('Quantified_KB.ax').

% include('Quantified_K.ax').
% In Logic K, no system finds a proof.

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

%----D1: A God-like being possesses all positive properties.
thf(defD1,definition,
    ( g
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [Phi: mu > $i > $o] :
              ( mimplies @ ( p @ Phi ) @ ( Phi @ X ) ) ) ) )).

%----C: Possibly, God exists. (Proved in C.p)
thf(corC,axiom,
    ( v
    @ ( mdia
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( g @ X ) ) ) )).

%----T2: Being God-like is an essence of any God-like being. (Proved in T2.p)
thf(thmT2,axiom,
    ( v
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mimplies @ ( g @ X ) @ ( ess @ g @ X ) ) ) )).

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

%----C2: God exists.
thf(corC2,conjecture,
    ( v  
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( g @ X ) ) )).

