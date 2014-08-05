
%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic KB.
include('Quantified_S4.ax').

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


%----A3: The property of being God-like is positive.
thf(axA3,axiom,
    ( v @ ( p @ g ) )).

%----A4: Positive properties are necessary positive properties.
thf(axA4,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mimplies @ ( p @ Phi ) @ ( mbox @ ( p @ Phi ) ) ) ) )).

%----D: Frode Bjordal's definition D: F is a positive property iff it is necessarily
%----the case that anything which is god-like has the property F.
thf(conD,conjecture,
    ( p
    = ( ^ [F: mu > $i > $o] :
          ( mbox
          @ ( mforall_ind
            @ ^ [X: mu] :
                ( mimplies @ ( g @ X ) @ ( F @ X ) ) ) ) ) )).