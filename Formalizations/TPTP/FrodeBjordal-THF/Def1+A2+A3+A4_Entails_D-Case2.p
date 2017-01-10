
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


%----A4: Positive properties are necessary positive properties.
thf(axA4,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mimplies @ ( p @ Phi ) @ ( mbox @ ( p @ Phi ) ) ) ) )).
   

%----D Case2   
thf(conDCase2,conjecture,
    ( v
    @ ( mforall_indset
      @ ^ [F: mu > $i > $o] :
          ( mimplies
          @ ( p @ F ) 
          @ ( mbox
            @ ( mforall_ind
              @ ^ [X: mu] :
                  ( mimplies @ ( g @ X ) @ ( F @ X ) ) ) ) ) ) )).
