%------------------------------------------------------------------------------
%----Axioms for Quantified Modal Logic KB.
include('Quantified_KB.ax').
%------------------------------------------------------------------------------
%----constant symbol for positive (p), God-like (g), essence (ess), necessary existence (ne)
thf(p_tp,type,(p:(mu>$i>$o)>$i>$o)).
thf(g_tp,type,(g:mu>$i>$o)).
thf(ess_tp,type,(ess:(mu>$i>$o)>mu>$i>$o)).
thf(ne_tp,type,(ne:mu>$i>$o)).
%----D1:A God-like being possesses all positive properties.
thf(defD1,definition,(g = (^[X:mu]:(mforall_indset@^[Phi:mu>$i>$o]:(mimplies@(p@Phi)@(Phi@X)))))).
%----C: Possibly, God exists. (Proved in C.p)
thf(corC,axiom,(v@(mdia@(mexists_ind@^[X:mu]:(g@X))))).
%----T2: Being God-like is an essence of any God-like being. (Proved in T2.p)
thf(thmT2,axiom,(v@(mforall_ind@^[X:mu]:(mimplies@(g@X)@(ess@g@X))))).
%----D3: Necessary existence of an individual is the necessary exemplification of all its essences
thf(defD3,definition,(ne = (^[X:mu]:(mforall_indset@^[Phi:mu>$i>$o]:
     (mimplies@(ess@Phi@X)@(mbox@(mexists_ind@^[Y:mu]:(Phi@Y)))))))).
%----A5:Necessary existence is positive.
thf(axA5,axiom,(v@(p@ne))).
%----T3: Necessarily God exists.
thf(thmT3,conjecture,(v@(mbox@(mexists_ind@^[X:mu]:(g@X))))).
