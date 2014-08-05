
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

%----constant symbol for: mcp
thf(mcp_tp,type,(
    mcp: ( mu > $i > $o ) > mu > $i > $o )).

%----constant symbol for: n
thf(n_tp,type,(
    n: mu > $i > $o )).   

%----D: Frode Bjordal's definition D: F is a positive property iff it is necessarily
%----the case that anything which is god-like has the property F.
thf(defD,definition,
    ( p
    = ( ^ [F: mu > $i > $o] :
          ( mbox
          @ ( mforall_ind
            @ ^ [X: mu] :
                ( mimplies @ ( g @ X ) @ ( F @ X ) ) ) ) ) )).   
   
thf(defD2,definition,
    ( mcp
    = ( ^ [F: mu > $i > $o,X: mu] :
          ( mand
          @ ( mand
            @ ( F @ X )
            @ ( p @ F ) )
          @ ( mforall_indset
             @ ^ [G: mu > $i > $o] :
                 ( mimplies
                 @ ( mand @ ( g @ X ) @ ( p @ g ) )
                 @ ( mbox
                   @ ( mforall_ind
                     @ ^ [Y: mu] :
                         ( mimplies @ ( F @ Y ) @ ( g @ Y ) ) ) ) ) ) ) ) )).

thf(defD3,definition,
    ( n
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [F: mu > $i > $o] :
              ( mimplies
              @ ( mcp @ F @ X )
              @ ( mbox
                @ ( mforall_ind
                  @ ^ [Y: mu] : ( F @ Y ) ) ) ) ) ) )).

%----A1: 
thf(axA1,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [F: mu > $i > $o] :
          ( mimplies
          @ ( p @ F )
          @ ( mnot @ ( p @ ^ [X: mu] : ( mnot @ ( F @ X ) ) ) ) ) ) )).

%----A2:
thf(axA2,axiom,
    ( v @ ( p @ n ) )).

%----Modal Collapse:
thf(prop_tp,type,(prop: $i > $o)).

thf(modalCollapse,conjecture,
    ( v @ ( mimplies @ prop @ ( mbox @ prop ) ) )). 