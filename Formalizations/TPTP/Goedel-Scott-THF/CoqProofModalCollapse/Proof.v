Add LoadPath "/Users/christophbenzmuellerimac/satallax-2.7/coq".
Require Import stttab.
Section SatallaxProblem.
Variable mu:SType.
Variable i:SType.
Variable rel : i --> i --> o.
Variable p : (mu --> i --> o) --> i --> o.
Variable g : mu --> i --> o.
Variable ne : mu --> i --> o.
Variable prop' : i --> o.
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
 := fun (Phi:mu --> i --> o) (X:mu) => mand (Phi X) (mforall_indset (fun (Psi:mu --> i --> o) => mimplies (Psi X) (mbox (mforall_ind (fun (Y:mu) => mimplies (Phi Y) (Psi Y)))))).
Hypothesis sym : msymmetric rel.
Hypothesis thmT2 : v (mforall_ind (fun (X:mu) => mimplies (g X) (ess g X))).
Hypothesis thmT3 : v (mbox (mexists_ind (fun (X:mu) => g X))).
Theorem modalCollapse : v (mimplies prop' (mbox prop')).

tab_start H0.
tab_negall H0 __1 H1.
tab_nor H1 H2 H3.
tab_negall H3 __2 H4.
tab_nor H4 H5 H6.
tab_all thmT3 (__2) H7.
tab_all thmT2 (__2) H8.
tab_all thmT3 (__1) H9.
tab_all H9 (__2) H10.
tab_all sym (__1) H11.
tab_all H11 (__2) H12.
tab_all H7 (__1) H13.
tab_imp H12 H14.
 tab_conflict H14 H5.
 tab_or H10 H15.
  tab_conflict H15 H5.
  tab_negall H15 __4 H16.
  tab_all H8 (__4) H17.
  tab_or H13 H18.
   tab_conflict H14 H18.
   tab_negall H18 __3 H19.
   tab_or H17 H20.
    tab_conflict H20 H16.
    tab_nor H20 H21 H22.
    tab_dn H22 H23.
    tab_all H23 (fun (X1:mu) (X2:i) => ~ prop' X2) H24.
    tab_or H24 H25.
     tab_conflict H6 H25.
     tab_all H25 (__1) H26.
     tab_or H26 H27.
      tab_conflict H14 H27.
      tab_all H27 (__3) H28.
      tab_or H28 H29.
       tab_conflict H29 H19.
       tab_conflict H29 H2.
Qed.
End SatallaxProblem.
