%------------------------------------------------------------------------------
% File     : PHI012+1 : TPTP v7.0.0. Released v7.0.0.
% Domain   : Philosophy
% Problem  : Lemma for Anselm's ontological argument
% Version  : [Wol16] axioms.
% English  :

% Refs     : [OZ11]  Oppenheimer & Zalta (2011), A Computationally-Discover
%          : [Wol16] Woltzenlogel Paleo (2016), Email to Geoff Sutcliffe
% Source   : [Wol16]
% Names    : lemma2.p [Wol16]

% Status   : Theorem
% Rating   : ? v7.0.0
% Syntax   : Number of formulae    :    3 (   0 unit)
%            Number of atoms       :   18 (   2 equality)
%            Maximal formula depth :    9 (   8 average)
%            Number of connectives :   16 (   1   ~;   2   |;   7   &)
%                                         (   1 <=>;   5  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    4 (   0 propositional; 1-3 arity)
%            Number of functors    :    3 (   3 constant; 0-0 arity)
%            Number of variables   :    7 (   0 sgn;   4   !;   3   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : See http://mally.stanford.edu/cm/ontological-argument/
%------------------------------------------------------------------------------
fof(definition_none_greater,axiom,(
    ! [X] :
      ( object(X)
     => ( exemplifies_property(none_greater,X)
      <=> ( exemplifies_property(conceivable,X)
          & ~ ? [Y] :
                ( object(Y)
                & exemplifies_relation(greater_than,Y,X)
                & exemplifies_property(conceivable,Y) ) ) ) ) )).

fof(connectedness_of_greater_than,axiom,(
    ! [X,Y] :
      ( ( object(X)
        & object(Y) )
     => ( exemplifies_relation(greater_than,X,Y)
        | exemplifies_relation(greater_than,Y,X)
        | X = Y ) ) )).

fof(lemma_2,conjecture,
    ( ? [X] :
        ( object(X)
        & exemplifies_property(none_greater,X) )
   => ? [X] :
        ( object(X)
        & exemplifies_property(none_greater,X)
        & ! [Y] :
            ( object(Y)
           => ( exemplifies_property(none_greater,Y)
             => Y = X ) ) ) )).

%------------------------------------------------------------------------------
