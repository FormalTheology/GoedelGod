
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


%----D Case1   
thf(conDCase1,conjecture,
    ( v
    @ ( mforall_indset
      @ ^ [F: mu > $i > $o] :
          ( mimplies
          @ ( mbox
            @ ( mforall_ind
              @ ^ [X: mu] :
                  ( mimplies @ ( g @ X ) @ ( F @ X ) ) ) )
          @ ( p @ F ) ) ) )).
