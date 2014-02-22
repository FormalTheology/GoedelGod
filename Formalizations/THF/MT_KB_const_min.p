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

%----A1: Either the property or its negation are positive, but not both.
thf(axA1,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mequiv
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

%----A4: Positive properties are necessary positive properties.
thf(axA4,axiom,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mimplies @ ( p @ Phi ) @ ( mbox @ ( p @ Phi ) ) ) ) )).

%----D2: An essence of an individual is a property possessed by it and
%----necessarily implying any of its properties
thf(defD2,definition,
    ( ess
    = ( ^ [Phi: mu > $i > $o,X: mu] :
          ( mand @ ( Phi @ X )
          @ ( mforall_indset
            @ ^ [Psi: mu > $i > $o] :
                ( mimplies @ ( Psi @ X )
                @ ( mbox
                  @ ( mforall_ind
                    @ ^ [Y: mu] :
                        ( mimplies @ ( Phi @ Y ) @ ( Psi @ Y ) ) ) ) ) ) ) ) )).

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




thf(mu_type,type,(
    mu: $tType ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mnot_type,type,(
    mnot: ( $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mnot,definition,
    ( mnot
    = ( ^ [Phi: $i > $o,W: $i] :
          ~ ( Phi @ W ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mor_type,type,(
    mor: ( $i > $o ) > ( $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mor,definition,
    ( mor
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          | ( Psi @ W ) ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mand_type,type,(
    mand: ( $i > $o ) > ( $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mand,definition,
    ( mand
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
          & ( Psi @ W ) ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mimplies_type,type,(
    mimplies: ( $i > $o ) > ( $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mimplies,definition,
    ( mimplies
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
         => ( Psi @ W ) ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mequiv_type,type,(
    mequiv: ( $i > $o ) > ( $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mequiv,definition,
    ( mequiv
    = ( ^ [Phi: $i > $o,Psi: $i > $o,W: $i] :
          ( ( Phi @ W )
        <=> ( Psi @ W ) ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mforall_ind_type,type,(
    mforall_ind: ( mu > $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mforall_ind,definition,
    ( mforall_ind
    = ( ^ [Phi: mu > $i > $o,W: $i] :
        ! [X: mu] :
          ( Phi @ X @ W ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mforall_indset_type,type,(
    mforall_indset: ( ( mu > $i > $o ) > $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mforall_indset,definition,
    ( mforall_indset
    = ( ^ [Phi: ( mu > $i > $o ) > $i > $o,W: $i] :
        ! [X: mu > $i > $o] :
          ( Phi @ X @ W ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mexists_ind_type,type,(
    mexists_ind: ( mu > $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mexists_ind,definition,
    ( mexists_ind
    = ( ^ [Phi: mu > $i > $o] :
          ( mnot
          @ ( mforall_ind
            @ ^ [X: mu] :
                ( mnot @ ( Phi @ X ) ) ) ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mequals_type,type,(
    mequals: mu > mu > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mequals,definition,
    ( mequals
    = ( ^ [X: mu,Y: mu,W: $i] : ( X = Y ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(rel_type,type,(
    rel: $i > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mbox_type,type,(
    mbox: ( $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mbox,definition,
    ( mbox
    = ( ^ [Phi: $i > $o,W: $i] :
        ! [V: $i] :
          ( ( rel @ W @ V )
         => ( Phi @ V ) ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mdia_type,type,(
    mdia: ( $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mdia,definition,
    ( mdia
    = ( ^ [Phi: $i > $o,W: $i] :
        ? [V: $i] :
          ( ( rel @ W @ V )
          & ( Phi @ V ) ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mvalid_type,type,(
    v: ( $i > $o ) > $o ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(mvalid,definition,
    ( v
    = ( ^ [Phi: $i > $o] :
        ! [W: $i] :
          ( Phi @ W ) ) ),
    unknown,
    [tpi_group(embedding),tpi_state(active)]).

thf(p_tp,type,(
    p: ( mu > $i > $o ) > $i > $o ),
    unknown,
    [tpi_group(sig),tpi_state(active)]).

thf(g_tp,type,(
    g: mu > $i > $o ),
    unknown,
    [tpi_group(sig),tpi_state(active)]).

thf(ess_tp,type,(
    ess: ( mu > $i > $o ) > mu > $i > $o ),
    unknown,
    [tpi_group(sig),tpi_state(active)]).

thf(ne_tp,type,(
    ne: mu > $i > $o ),
    unknown,
    [tpi_group(sig),tpi_state(active)]).

thf(thmFG_con,conjecture,
    ( v
    @ ( mforall_indset
      @ ^ [Phi: mu > $i > $o] :
          ( mforall_ind
          @ ^ [X: mu] :
              ( mimplies @ ( g @ X ) @ ( mimplies @ ( mnot @ ( p @ Phi ) ) @ ( mnot @ ( Phi @ X ) ) ) ) ) ) ),
    unknown,
    [tpi_group(fg),tpi_state(active)]).

thf(defD1,definition,
    ( g
    = ( ^ [X: mu] :
          ( mforall_indset
          @ ^ [Phi: mu > $i > $o] :
              ( mimplies @ ( p @ Phi ) @ ( Phi @ X ) ) ) ) ),
    unknown,
    [tpi_group(d1),tpi_state(active)]).

thf(thmMT_con,conjecture,
    ( v
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mimplies @ ( g @ X ) @ ( mimplies @ ( g @ Y ) @ ( mequals @ X @ Y ) ) ) ) ) ),
    unknown,
    [tpi_group(mt),tpi_state(active)]).