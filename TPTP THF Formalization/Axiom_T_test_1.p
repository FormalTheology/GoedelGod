%----Axioms for Quantified Modal Logic S5 (providing quantification over 
%----individuals, propositions, sets of individuals, sets of sets of individual).

include('Quantified_S5.ax').

%------------------------------------------------------------------------------

% This test illustrates that axiom T is implied in our embedding
% of modal logics; it actually follows from postulated reflexivity
% of the accessibility relation rel_s5.
% LEO-II proves it quickly
   
%----Conjecture 
thf(thm,conjecture,
    ( mvalid @
      ( mforall_prop @
        ^[P: $i > $o] :
          ( mimplies @
            ( mbox_s5 @ P ) @
            P ) ) )).
