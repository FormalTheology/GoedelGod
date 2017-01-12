%------------------------------------------------------------------------------
% File     : PHI010+1 : TPTP v7.0.0. Released v7.0.0.
% Domain   : Philosophy
% Problem  : Lemma for Anselm's ontological argument
% Version  : [Wol16] axioms.
% English  :

% Refs     : [OZ11]  Oppenheimer & Zalta (2011), A Computationally-Discover
%          : [Wol16] Woltzenlogel Paleo (2016), Email to Geoff Sutcliffe
% Source   : [Wol16]
% Names    : lemma1.p [Wol16]

% Status   : Theorem
% Rating   : ? v7.0.0
% Syntax   : Number of formulae    :    5 (   0 unit)
%            Number of atoms       :   25 (   4 equality)
%            Maximal formula depth :   13 (   7 average)
%            Number of connectives :   21 (   1   ~;   0   |;  11   &)
%                                         (   1 <=>;   8  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   13 (   0 sgn;  12   !;   1   ?)
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

fof(description_axiom_identity_instance,axiom,(
    ! [F,X,W] :
      ( ( property(F)
        & object(X)
        & object(W) )
     => ( ( is_the(X,F)
          & X = W )
      <=> ? [Y] :
            ( object(Y)
            & exemplifies_property(F,Y)
            & ! [Z] :
                ( object(Z)
               => ( exemplifies_property(F,Z)
                 => Z = Y ) )
            & Y = W ) ) ) )).

fof(lemma_1,conjecture,(
    ! [X,F,Y] :
      ( ( object(X)
        & property(F)
        & object(Y) )
     => ( ( is_the(X,F)
          & X = Y )
       => exemplifies_property(F,Y) ) ) )).

%------------------------------------------------------------------------------
