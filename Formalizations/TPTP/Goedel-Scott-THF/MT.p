
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