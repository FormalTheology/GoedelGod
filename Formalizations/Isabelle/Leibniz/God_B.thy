theory God_B
imports AoC

begin
consts E :: "c" ("E!")
consts G :: "c" ("G")

definition N :: "c \<Rightarrow> bool" where "N A \<equiv> \<not> P (\<^bold>~ A) "

axiomatization where
NG: "N G"

(* (ii) Whenever something doesn’t exist, it possibly doesn’t exist. *)
lemma Two: "\<forall>X. (\<not>(X \<^bold>\<in> E!)) \<longrightarrow> (P (conjunction X (not E!)))"
by (simp add: POSS2)

(* (iii) Whenever something possibly doesn’t exist, it is falsely maintained to be impossible not to exist. *)
lemma Three: "\<forall>X. (P (conjunction X (not E!))) \<longrightarrow> \<not> (\<not> (P (conjunction X (not E!)))) "
by simp

(* (iv) Whenever something is falsely maintained to be impossible not to exist,
then it is falsely maintained to be necessary. (For necessary is what is
impossible not to exist.) *)

(* this is the closest to what Leibniz actually said *)
lemma Four: "\<forall>X. \<not> (\<not> (P (conjunction X (not E!)))) \<longrightarrow> \<not> (N X) "
nitpick[user_axioms = true] oops

(* Modified statement (iv): Whenever something is falsely maintained to be impossible not to exist,
then it is falsely maintained to be necessary to exist *)
lemma Four2: "\<forall>X. \<not> (\<not> (P (conjunction X (not E!)))) \<longrightarrow> \<not> (N (conjunction X E!) ) "
by (meson CONJ5 NEG2 N_def POSS1)
(* it surprises me that this lemma can be proven *)

(* Modified statement (iv): Whenever something is falsely maintained to be impossible not to exist,
then implication of its existence is falsely maintained to be necessary *)
(* note that "not X or E!" is equivalent to  "X implies E!" *)
lemma Four3: "\<forall>X. \<not> (\<not> (P (conjunction X (not E!)))) \<longrightarrow> \<not> (N (disjunction (not X) E!))"
by (smt CONJ1 CONJ4 CONJ5 CONT2 IDEN2 NEG1 N_def POSS1 disjunction_def equal_def) 
(* ToDo: set option "smt_timeout" in order to increase the timeout*)

(* Four4 is logically equivalent to Four3, but easier to prove *)
lemma Four4: "\<forall>X. \<not> (\<not> (P (conjunction X (not E!)))) \<longrightarrow> \<not> (N (not (conjunction X (not E!))))"
using NEG1 N_def POSS1 equal_def by blast

(* I think Four3 is the best translation of Leibniz's sentence *)

(*(i) By hypothesis, the necessary being doesn‘t exist.*)
(*(v) Therefore the necessary being is falsely maintained to be necessary. *)
lemma Five: "(\<not> (G \<^bold>\<in> E)) \<longrightarrow> \<not> (N (disjunction (not G) E!))"
by (simp add: Four3 Two)


(* ToDo... *)

  (* (vi) This conclusion is either true or false. *)
  
  (* (vii) If it is true, it follows that the necessary being contains a contradiction,
or is impossible, because contradictory assertions have been proved about it,
namely that it is not necessary. For a contradictory conclusion can only be
shown about a thing which implies a contradiction. *)
  
  (* (viii) If it is false, necessarily one of the premises must be false. But the only
premise that might be false is the hypothesis saying that the necessary being
doesn’t exist. *)
  
  (* (ix) Hence we conclude that the necessary being either is impossible, or it
exists. *)
  
  (* (x) So if we define GOD as an “Ens a se”, i.e. a being from whose essence
its existence follows, i.e. a necessary being, it follows that GOD, if he is
possible, actually exists. *)

end