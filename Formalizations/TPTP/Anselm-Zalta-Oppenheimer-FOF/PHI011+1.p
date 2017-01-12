%------------------------------------------------------------------------------
% File     : PHI011+1 : TPTP v7.0.0. Released v7.0.0.
% Domain   : Philosophy
% Problem  : Lemma for Anselm's ontological argument
% Version  : [Wol16] axioms.
% English  :

% Refs     : [OZ11]  Oppenheimer & Zalta (2011), A Computationally-Discover
%          : [Wol16] Woltzenlogel Paleo (2016), Email to Geoff Sutcliffe
% Source   : [Wol16]
% Names    : descripthm2.p [Wol16]

% Status   : Theorem
% Rating   : ? v7.0.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   20 (   1 equality)
%            Maximal formula depth :    7 (   6 average)
%            Number of connectives :   16 (   1   ~;   0   |;   6   &)
%                                         (   0 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   11 (   0 sgn;  10   !;   1   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : See http://mally.stanford.edu/cm/ontological-argument/
%------------------------------------------------------------------------------
fof(objects_are_not_properties,axiom,(
    ! [X] :
      ( object(X)
     => ~ property(X) ) )).

fof(exemplifier_is_object_and_exemplified_is_property,axiom,(
    ! [X,F] :
      ( exemplifies_property(F,X)
     => ( property(F)
        & object(X) ) ) )).

fof(description_is_property_and_described_is_object,axiom,(
    ! [X,F] :
      ( is_the(X,F)
     => ( property(F)
        & object(X) ) ) )).

fof(lemma_1,axiom,(
    ! [X,F,Y] :
      ( ( object(X)
        & property(F)
        & object(Y) )
     => ( ( is_the(X,F)
          & X = Y )
       => exemplifies_property(F,Y) ) ) )).

fof(description_theorem_2,conjecture,(
    ! [F] :
      ( property(F)
     => ( ? [Y] :
            ( object(Y)
            & is_the(Y,F) )
       => ! [Z] :
            ( object(Z)
           => ( is_the(Z,F)
             => exemplifies_property(F,Z) ) ) ) ) )).

%------------------------------------------------------------------------------
