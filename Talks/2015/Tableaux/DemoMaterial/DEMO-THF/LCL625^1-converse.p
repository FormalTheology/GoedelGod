%------------------------------------------------------------------------------
% File     : LCL625^1 : TPTP v6.0.0. Released v3.6.0.
% Domain   : Logical Calculi
% Problem  : GL/K4 axiom is valid in this frame
% Version  : [Ben08] axioms.
% English  : In a frame that is transitive and upwards well-founded, the GL/K4
%            axiom is valid.

% Refs     : [Fit07] Fitting (2007), Modal Proof Theory
%          : [Ben08] Benzmueller (2008), Email to G. Sutcliffe
% Source   : [Ben08]
% Names    : Fitting-HB-13 [Ben08]
%          : Fitting-HB-15 [Ben08]

% Status   : Theorem
% Rating   : 0.14 v5.5.0, 0.17 v5.4.0, 0.40 v5.2.0, 0.60 v5.1.0, 0.40 v4.1.0, 0.00 v4.0.1, 0.33 v3.7.0
% Syntax   : Number of formulae    :   79 (   2 unit;  41 type;  36 defn)
%            Number of atoms       :  440 (  40 equality; 153 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  137 (   6   ~;   3   |;  15   &; 103   @)
%                                         (   1 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  226 ( 226   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   47 (  41   :)
%            Number of variables   :  111 (   2 sgn;  25   !;  10   ?;  76   ^)
%                                         ( 111   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include simple maths definitions and axioms
include('Axioms/LCL008^0.ax').
include('Axioms/SET008^2.ax').
%------------------------------------------------------------------------------


%----Axioms
thf(loeb,axiom,(
    ! [R: $i > $i > $o,P: $i > $o] :
      ( mvalid @ ( mimpl @ ( mbox @ R @ ( mimpl @ ( mbox @ R @ P ) @ P ) ) @ ( mbox @ R @ P ) ) ) )).


%----Conjecture
thf(upwf_trans,conjecture,(
    ! [R: $i > $i > $o] :
      ( ( transitive @ R )
      & ( upwards_well_founded @ R ) ) )).
%------------------------------------------------------------------------------
