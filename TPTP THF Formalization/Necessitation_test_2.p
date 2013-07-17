%----Axioms for Quantified Modal Logic S5 (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_S5.ax').

%------------------------------------------------------------------------------

% This test illustrates that the necessitation rule is implied in our embedding
% of modal logics;
% LEO-II prove it quickly

   thf(p,type, p: $i > $o ).
   
%----Axiom 
thf(ax,axiom,
    ( mvalid @ p ) ).

   
%----Conjecture 
thf(thm,conjecture,
    ( mvalid @ ( mbox_s5 @ p ) )).
