%------------------------------------------------------------------------------
%----Include simple maths definitions and axioms
include('LCL008^0.ax').
include('SET008^2.ax').
%------------------------------------------------------------------------------
%----Axioms
thf(test,axiom,( (! [R: $i > $i > $o] :
       ( ( ( transitive @ R )
           & ( upwards_well_founded @ R ) )
         =>
         ( mvalid @ ( mimpl @ ( mbox @ R @ ( mimpl @ ( mbox @ R @ P ) @ P ) ) @ ( mbox @ R @ P ) ) ) ) ) )).

%------------------------------------------------------------------------------
