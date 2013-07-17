%----Axioms for Quantified Modal Logic S5 (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_S5.ax').

%------------------------------------------------------------------------------

% This test illustrates that the necessitation rule is modelled correctly
% in our approach; this test conjecture should not be provable;
% LEO-II fails to prove it
% Nitrox and Satallax confirm that it is CounterSatisfiable

thf(p,type, p: $i > $o ).
   
%----Conjecture 
thf(thm,conjecture,
    ( mvalid @
      ( mimplies @ p @ ( mbox_s5 @ p ) ) )).
