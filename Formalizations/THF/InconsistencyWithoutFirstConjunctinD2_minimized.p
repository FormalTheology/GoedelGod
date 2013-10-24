%----We work with logic KB 
%----We reserve an accessibility relation constant rel
thf(rel_type,type,(
    rel: $i > $i > $o )).
%----   
thf(sym,axiom,
    ( ! [V: $i, Z: $i]: ( ( rel @ V @ Z ) => ( rel @ Z @ V ) ) )).

%----type $i stands for possible worlds
%----type mu stands for individuals
thf(mu_type,type,(
    mu: $tType )).

%----Modal operators not, and, implies, box, diamond
thf(mnot_type,type,(
    mnot: ( $i > $o ) > $i > $o )).

thf(mnot,definition,
    ( mnot
    = ( ^ [Phi: $i > $o,W: $i] :
          ~ ( Phi @ W ) ) )).

thf(mand_type,type,(
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o )).

thf(mand,definition,
    ( mand
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          & ( Psi @ W ) ) ) )).

thf(mimplies_type,type,(
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o )).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          => ( Psi @ W ) ) ) )).

thf(mbox_type,type,(
    mbox: ( $i > $i > $o ) > ( $i > $o ) > $i > $o )).

thf(mbox,definition,
    ( mbox
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ~ ( rel @ W @ V )
          | ( Phi @ V ) ) ) )).

thf(mdia_type,type,(
    mdia: ( $i > $i > $o ) > ( $i > $o ) > $i > $o )).

thf(mdia,definition,
    ( mdia
    = ( ^ [Phi: $i > $o,W: $i] :
        ? [V: $i] :
          ( ( rel @ W @ V )
          & ( Phi @ V ) ) ) )).

%----Modal quantifier (as constant Pi) for individuals and propositions 

thf(mforall_ind_type,type,(
    mforall_ind: ( mu > $i > $o ) > $i > $o )).

thf(mforall_ind,definition,
    ( mforall_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ! [X: mu] :
          ( Phi @ X @ W ) ) )).

thf(mexists_ind_type,type,(
    mexists_ind: ( mu > $i > $o ) > $i > $o )).

thf(mexists_ind,definition,
    ( mexists_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ? [X: mu] :
          ( Phi @ X @ W ) ) )).

%----Modal quantifier for sets of individuals
%----this is new!

thf(mforall_indset_type,type,(
    mforall_indset: ( ( mu > $i > $o ) > $i > $o ) > $i > $o )).

thf(mforall_indset,definition,
    ( mforall_indset
    = ( ^ [Phi: ( mu > $i > $o ) > $i > $o,W: $i] :
        ! [X: mu > $i > $o] :
          ( Phi @ X @ W ) ) )).

%----Definition of validity
thf(v_type,type,(
    v: ( $i > $o ) > $o )).

thf(mvalid,definition,
    ( v
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ( Phi @ W ) ) )).

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
thf(axA1a,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mimplies
          @ ( p
            @ ^ [X: mu] :
                ( mnot @ ( Phi @ X ) ) )
          @ ( mnot @ ( p @ Phi ) ) ) ) )).

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

%----D2: An essence of an individual is a property possessed by it and
%----necessarily implying any of its properties
thf(defD2,definition,
    ( ess
    = ( ^ [Phi: mu > $i > $o,X: mu] :
          ( mforall_indset
          @ ^ [Psi: mu > $i > $o] :
              ( mimplies @ ( Psi @ X )
              @ ( mbox
                @ ( mforall_ind
                  @ ^ [Y: mu] :
                      ( mimplies @ ( Phi @ Y ) @ ( Psi @ Y ) ) ) ) ) ) ) )).

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


%----Conjecture False
thf(con,conjecture, $false ).   