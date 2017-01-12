%------------------------------------------------------------------------------
% File     : PHI014+1 : TPTP v7.0.0. Released v7.0.0.
% Domain   : Philosophy
% Problem  : Anselm's ontological argument, simplified
% Version  : [Wol16] axioms.
% English  :

% Refs     : [OZ11]  Oppenheimer & Zalta (2011), A Computationally-Discover
%          : [Wol16] Woltzenlogel Paleo (2016), Email to Geoff Sutcliffe
% Source   : [Wol16]
% Names    : ontological-simplified.p [Wol16]

% Status   : Theorem
% Rating   : ? v7.0.0
% Syntax   : Number of formulae    :    6 (   2 unit)
%            Number of atoms       :   23 (   0 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   19 (   2   ~;   0   |;   8   &)
%                                         (   1 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   5 constant; 0-0 arity)
%            Number of variables   :    9 (   0 sgn;   6   !;   3   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : See http://mally.stanford.edu/cm/ontological-argument/
%          : This contains only the axioms used by Prover9 in it's proof.
%------------------------------------------------------------------------------
fof(description_theorem_2,axiom,(
    ! [F] :
      ( property(F)
     => ( ? [Y] :
            ( object(Y)
            & is_the(Y,F) )
       => ! [Z] :
            ( object(Z)
           => ( is_the(Z,F)
             => exemplifies_property(F,Z) ) ) ) ) )).

fof(description_is_property_and_described_is_object,axiom,(
    ! [X,F] :
      ( is_the(X,F)
     => ( property(F)
        & object(X) ) ) )).

fof(definition_none_greater,axiom,(
    ! [X] :
      ( object(X)
     => ( exemplifies_property(none_greater,X)
      <=> ( exemplifies_property(conceivable,X)
          & ~ ? [Y] :
                ( object(Y)
                & exemplifies_relation(greater_than,Y,X)
                & exemplifies_property(conceivable,Y) ) ) ) ) )).

fof(premise_2,axiom,(
    ! [X] :
      ( object(X)
     => ( ( is_the(X,none_greater)
          & ~ exemplifies_property(existence,X) )
       => ? [Y] :
            ( object(Y)
            & exemplifies_relation(greater_than,Y,X)
            & exemplifies_property(conceivable,Y) ) ) ) )).

fof(definition_god,axiom,(
    is_the(god,none_greater) )).

fof(god_exists,conjecture,(
    exemplifies_property(existence,god) )).

%------------------------------------------------------------------------------
