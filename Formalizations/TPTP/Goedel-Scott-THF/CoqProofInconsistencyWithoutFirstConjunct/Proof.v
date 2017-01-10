Add LoadPath "./".
Require Import stttab.
Section SatallaxProblem.
Variable mu:SType.
Variable i:SType. 
Variable rel : i --> i --> o.
Variable p : (mu --> i --> o) --> i --> o.
Variable g : mu --> i --> o.
Definition mnot : (i --> o) --> i --> o
 := fun (Phi:i --> o) (W:i) => ~ Phi W.
Definition mor : (i --> o) --> (i --> o) --> i --> o
 := fun (Phi:i --> o) (Psi:i --> o) (W:i) => Phi W \/ Psi W.
Definition mbox_generic : (i --> i --> o) --> (i --> o) --> i --> o
 := fun (R:i --> i --> o) (Phi:i --> o) (W:i) => forall (V:i), ~ R W V \/ Phi V.
Definition mforall_ind : (mu --> i --> o) --> i --> o
 := fun (Phi:mu --> i --> o) (W:i) => forall (X:mu), Phi X W.
Definition mforall_indset : ((mu --> i --> o) --> i --> o) --> i --> o
 := fun (Phi:(mu --> i --> o) --> i --> o) (W:i) => forall (X:mu --> i --> o), Phi X W.
Definition mand : (i --> o) --> (i --> o) --> i --> o
 := fun (Phi:i --> o) (Psi:i --> o) => mnot (mor (mnot Phi) (mnot Psi)).
Definition mimplies : (i --> o) --> (i --> o) --> i --> o
 := fun (Phi:i --> o) (Psi:i --> o) => mor (mnot Phi) Psi.
Definition mequiv : (i --> o) --> (i --> o) --> i --> o
 := fun (Phi:i --> o) (Psi:i --> o) => mand (mimplies Phi Psi) (mimplies Psi Phi).
Definition mdia_generic : (i --> i --> o) --> (i --> o) --> i --> o
 := fun (R:i --> i --> o) (Phi:i --> o) => mnot (mbox_generic R (mnot Phi)).
Definition mexists_ind : (mu --> i --> o) --> i --> o
 := fun (Phi:mu --> i --> o) => mnot (mforall_ind (fun (X:mu) => mnot (Phi X))).
Definition mexists_indset : ((mu --> i --> o) --> i --> o) --> i --> o
 := fun (Phi:(mu --> i --> o) --> i --> o) => mnot (mforall_indset (fun (X:mu --> i --> o) => mnot (Phi X))).
Definition v : (i --> o) --> o
 := fun (Phi:i --> o) => forall (W:i), Phi W.
Definition msymmetric : (i --> i --> o) --> o
 := fun (R:i --> i --> o) => forall (S:i) (T:i), R S T -> R T S.
Definition mbox : (i --> o) --> i --> o
 := mbox_generic rel.
Definition mdia : (i --> o) --> i --> o
 := mdia_generic rel.
Definition ess : (mu --> i --> o) --> mu --> i --> o
 := fun (Phi:mu --> i --> o) (X:mu) => mforall_indset (fun (Psi:mu --> i --> o) => mimplies (Psi X) (mbox (mforall_ind (fun (Y:mu) => mimplies (Phi Y) (Psi Y))))).
Definition ne : mu --> i --> o
 := fun (X:mu) => mforall_indset (fun (Phi:mu --> i --> o) => mimplies (ess Phi X) (mbox (mexists_ind (fun (Y:mu) => Phi Y)))).
Hypothesis sym : msymmetric rel.
Hypothesis axA1a : v (mforall_indset (fun (Phi:mu --> i --> o) => mimplies (p (fun (X:mu) => mnot (Phi X))) (mnot (p Phi)))).
Hypothesis axA2 : v (mforall_indset (fun (Phi:mu --> i --> o) => mforall_indset (fun (Psi:mu --> i --> o) => mimplies (mand (p Phi) (mbox (mforall_ind (fun (X:mu) => mimplies (Phi X) (Psi X))))) (p Psi)))).
Hypothesis axA5 : v (p ne).
Theorem claim : False.
tab_start H0.
tab_inh (i) __0.
tab_all sym (__0) H1.
tab_all axA1a (__0) H2.
tab_all axA2 (__0) H3.
tab_all axA5 (__0) H4.
tab_all H2 (fun (X1:mu) (X2:i) => forall (X3:mu --> i --> o), (forall (X4:mu --> i --> o), X4 X1 X2 -> (forall (X5:i), rel X2 X5 -> (forall (X6:mu), X3 X6 X5 -> X4 X6 X5))) -> (forall (X4:i), rel X2 X4 -> (~ (forall (X5:mu), ~ X3 X5 X4)))) H5.
tab_all H3 (fun (X1:mu) (X2:i) => forall (X3:mu --> i --> o), (forall (X4:mu --> i --> o), X4 X1 X2 -> (forall (X5:i), rel X2 X5 -> (forall (X6:mu), X3 X6 X5 -> X4 X6 X5))) -> (forall (X4:i), rel X2 X4 -> (~ (forall (X5:mu), ~ X3 X5 X4)))) H6.
tab_all H6 (fun (X1:mu) (X2:i) => ~ (forall (X3:mu --> i --> o), (forall (X4:mu --> i --> o), X4 X1 X2 -> (forall (X5:i), rel X2 X5 -> (forall (X6:mu), X3 X6 X5 -> X4 X6 X5))) -> (forall (X4:i), rel X2 X4 -> (~ (forall (X5:mu), ~ X3 X5 X4))))) H7.
tab_or H5 H8.
 tab_or H7 H9.
  tab_dn H9 H10.
  tab_or H10 H11.
   tab_rew_or H4 H12 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), X1 (mnot (ess X4 X2) X3) (mbox (mexists_ind (fun (X5:mu) => X4 X5)) X3)) __0) .
   tab_rew_dn H12 H13 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), X1 (ess X4 X2 X3) -> mbox (mexists_ind (fun (X5:mu) => X4 X5)) X3) __0) .
   tab_rew_or H13 H14 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X1 (mnot (X5 X2) X3) (mbox (mforall_ind (fun (X6:mu) (X7:i) => mnot (X4 X6) X7 \/ X5 X6 X7)) X3)) -> mbox (mexists_ind (fun (X5:mu) => X4 X5)) X3) __0) .
   tab_rew_dn H14 H15 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X1 (X5 X2 X3) -> mbox (mforall_ind (fun (X6:mu) (X7:i) => ~ X4 X6 X7 \/ X5 X6 X7)) X3) -> mbox (mexists_ind (fun (X5:mu) => X4 X5)) X3) __0) .
   tab_rew_or H15 H16 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), X1 (~ rel X3 X6) (mforall_ind (fun (X7:mu) (X8:i) => ~ X4 X7 X8 \/ X5 X7 X8) X6))) -> (forall (X5:i), ~ rel X3 X5 \/ mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
   tab_rew_dn H16 H17 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), X1 (rel X3 X6) -> mforall_ind (fun (X7:mu) (X8:i) => ~ X4 X7 X8 \/ X5 X7 X8) X6)) -> (forall (X5:i), ~ rel X3 X5 \/ mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
   tab_rew_or H17 H18 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), rel X3 X6 -> (forall (X7:mu), X1 (~ X4 X7 X6) (X5 X7 X6)))) -> (forall (X5:i), ~ rel X3 X5 \/ mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
   tab_rew_dn H18 H19 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), rel X3 X6 -> (forall (X7:mu), X1 (X4 X7 X6) -> X5 X7 X6))) -> (forall (X5:i), ~ rel X3 X5 \/ mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
   tab_rew_or H19 H20 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), rel X3 X6 -> (forall (X7:mu), X4 X7 X6 -> X5 X7 X6))) -> (forall (X5:i), X1 (~ rel X3 X5) (mexists_ind (fun (X6:mu) => X4 X6) X5))) __0) .
   tab_rew_dn H20 H21 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), rel X3 X6 -> (forall (X7:mu), X4 X7 X6 -> X5 X7 X6))) -> (forall (X5:i), X1 (rel X3 X5) -> mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
   tab_conflict H21 H11.
   tab_negall H11 __1 H22.
   tab_nor H22 H23 H24.
   tab_negall H24 __2 H25.
   tab_nor H25 H26 H27.
   tab_all H1 (__1) H28.
   tab_dn H26 H29.
   tab_all H29 (fun (X1:mu) (X2:i) => False) H30.
   tab_imp H28 H31.
    tab_conflict H31 H23.
    tab_imp H30 H32.
     tab_negall H32 __3 H33.
     tab_negimp H33 H34 H35.
     tab_negall H35 __5 H36.
     tab_negimp H36 H37 H38.
     tab_negall H38 __6 H39.
     tab_negimp H39 H40 H41.
     tab_false H40.
     tab_all H32 (__0) H42.
     tab_imp H42 H43.
      tab_conflict H31 H43.
      tab_negall H43 __4 H44.
      tab_dn H44 H45.
      tab_false H45.
  tab_conflict H9 H8.
 tab_rew_or H4 H46 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), X1 (mnot (ess X4 X2) X3) (mbox (mexists_ind (fun (X5:mu) => X4 X5)) X3)) __0) .
 tab_rew_dn H46 H47 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), X1 (ess X4 X2 X3) -> mbox (mexists_ind (fun (X5:mu) => X4 X5)) X3) __0) .
 tab_rew_or H47 H48 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X1 (mnot (X5 X2) X3) (mbox (mforall_ind (fun (X6:mu) (X7:i) => mnot (X4 X6) X7 \/ X5 X6 X7)) X3)) -> mbox (mexists_ind (fun (X5:mu) => X4 X5)) X3) __0) .
 tab_rew_dn H48 H49 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X1 (X5 X2 X3) -> mbox (mforall_ind (fun (X6:mu) (X7:i) => ~ X4 X6 X7 \/ X5 X6 X7)) X3) -> mbox (mexists_ind (fun (X5:mu) => X4 X5)) X3) __0) .
 tab_rew_or H49 H50 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), X1 (~ rel X3 X6) (mforall_ind (fun (X7:mu) (X8:i) => ~ X4 X7 X8 \/ X5 X7 X8) X6))) -> (forall (X5:i), ~ rel X3 X5 \/ mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
 tab_rew_dn H50 H51 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), X1 (rel X3 X6) -> mforall_ind (fun (X7:mu) (X8:i) => ~ X4 X7 X8 \/ X5 X7 X8) X6)) -> (forall (X5:i), ~ rel X3 X5 \/ mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
 tab_rew_or H51 H52 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), rel X3 X6 -> (forall (X7:mu), X1 (~ X4 X7 X6) (X5 X7 X6)))) -> (forall (X5:i), ~ rel X3 X5 \/ mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
 tab_rew_dn H52 H53 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), rel X3 X6 -> (forall (X7:mu), X1 (X4 X7 X6) -> X5 X7 X6))) -> (forall (X5:i), ~ rel X3 X5 \/ mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
 tab_rew_or H53 H54 (fun (X1:o --> o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), rel X3 X6 -> (forall (X7:mu), X4 X7 X6 -> X5 X7 X6))) -> (forall (X5:i), X1 (~ rel X3 X5) (mexists_ind (fun (X6:mu) => X4 X6) X5))) __0) .
 tab_rew_dn H54 H55 (fun (X1:o --> o) => p (fun (X2:mu) (X3:i) => forall (X4:mu --> i --> o), (forall (X5:mu --> i --> o), X5 X2 X3 -> (forall (X6:i), rel X3 X6 -> (forall (X7:mu), X4 X7 X6 -> X5 X7 X6))) -> (forall (X5:i), X1 (rel X3 X5) -> mexists_ind (fun (X6:mu) => X4 X6) X5)) __0) .
 tab_conflict H55 H8.
Qed.
End SatallaxProblem.
