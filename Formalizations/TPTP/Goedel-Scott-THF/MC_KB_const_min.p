%----Goedel's Ontological Proof of the Existence of God
%----
%----Formalization and Automation using an 
%----Embedding of Quantified (Multi-)Modallogic in THF (HOL)
%----
%----Authors: Christoph Benzmueller and Bruno Woltzenlogel-Paleo
%----July, 16 2013 (update on August 21, 2013)

%----Informal: Scott's version of Goedel's ontological proof
%              Here we are interested in the consistency of the
%              axioms and definitions.


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

%----T2: Being God-like is an essence of any God-like being.
thf(thmT2,lemma,
    ( v
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mimplies @ ( g @ X ) @ ( ess @ g @ X ) ) ) )).

%----T3: Necessarily God exists.
thf(thmT3,lemma,
    ( v
    @ ( mbox
      @ ( mexists_ind
        @ ^ [X: mu] :
            ( g @ X ) ) ) )).

%----Modal Collapse:
thf(prop_tp,type,(prop: $i > $o)).

thf(modalCollapse,conjecture,
    ( v @ ( mimplies @ prop @ ( mbox @ prop ) ) )). 