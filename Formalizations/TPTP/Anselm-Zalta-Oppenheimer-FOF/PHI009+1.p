%------------------------------------------------------------------------------
% File     : PHI009+1 : TPTP v7.0.0. Released v7.0.0.
% Domain   : Philosophy
% Problem  : Lemma for Anselm's ontological argument
% Version  : [Wol16] axioms.
% English  :

% Refs     : [OZ11]  Oppenheimer & Zalta (2011), A Computationally-Discover
%          : [Wol16] Woltzenlogel Paleo (2016), Email to Geoff Sutcliffe
% Source   : [Wol16]
% Names    : descripthm1.p [Wol16]

% Status   : Theorem
% Rating   : ? v7.0.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :   19 (   2 equality)
%            Maximal formula depth :   13 (  12 average)
%            Number of connectives :   17 (   0   ~;   0   |;   9   &)
%                                         (   1 <=>;   7  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    9 (   0 sgn;   6   !;   3   ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : See http://mally.stanford.edu/cm/ontological-argument/
%------------------------------------------------------------------------------
fof(description_axiom_schema_instance,axiom,(
    ! [F,G,X] :
      ( ( property(F)
        & property(G)
        & object(X) )
     => ( ( is_the(X,F)
          & exemplifies_property(G,X) )
      <=> ? [Y] :
            ( object(Y)
            & exemplifies_property(F,Y)
            & ! [Z] :
                ( object(Z)
               => ( exemplifies_property(F,Z)
                 => Z = Y ) )
            & exemplifies_property(G,Y) ) ) ) )).

fof(description_theorem_1,conjecture,(
    ! [F] :
      ( property(F)
     => ( ? [Y] :
            ( object(Y)
            & exemplifies_property(F,Y)
            & ! [Z] :
                ( object(Z)
               => ( exemplifies_property(F,Z)
                 => Z = Y ) ) )
       => ? [U] :
            ( object(U)
            & is_the(U,F) ) ) ) )).

%------------------------------------------------------------------------------
