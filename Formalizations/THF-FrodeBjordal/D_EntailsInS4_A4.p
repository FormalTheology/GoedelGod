
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

%----D: Frode Bjordal's definition D: F is a positive property iff it is necessarily
%----the case that anything which is god-like has the property F.
thf(defD,definition,
    ( p
    = ( ^ [F: mu > $i > $o] :
          ( mbox
          @ ( mforall_ind
            @ ^ [X: mu] :
                ( mimplies @ ( g @ X ) @ ( F @ X ) ) ) ) ) )).

%----A4: Positive properties are necessary positive properties.
thf(conA4,conjecture,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mimplies @ ( p @ Phi ) @ ( mbox @ ( p @ Phi ) ) ) ) )).


