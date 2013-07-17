%----Axioms for Quantified Modal Logic S5 (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_S5.ax').

%------------------------------------------------------------------------------

% This test illustrates that the necessitation rule is implied in our embedding
% of modal logics
% LEO-II fails to prove it
   
%----Conjecture 
thf(thm,conjecture,
    ( ![P: $i > $o] :
       ( ( mvalid @ P )
         =>
         ( mvalid @ ( mbox_s5 @ P ) ) ) )).
