
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

%----D: Frode Bjordal's definition D: F is a positive property iff it is necessarily
%----the case that anything which is god-like has the property F.
thf(defD,definition,
    ( p
    = ( ^ [F: mu > $i > $o] :
          ( mbox
          @ ( mforall_ind
            @ ^ [X: mu] :
                ( mimplies @ ( g @ X ) @ ( F @ X ) ) ) ) ) )).

%----A3: The property of being God-like is positive.
thf(conA3,conjecture,
    ( v @ ( p @ g ) )).

