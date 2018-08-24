theory Mereotopology
imports Mereology
begin

text {*This is a presentation in Isabelle/HOL of Mereotopology. The presentation is based on ``Parts
and Places'' by Roberto Casati and Achille Varzi @{cite "casati_parts_1999"}, as well as Varzi's
``Parts, Wholes and Part-Whole Relations: The Prospects of Mereotopology'' @{cite "varzi_parts_1996"}. *}

text {* Please note that this is an extremely ROUGH DRAFT. *}

text{* In this file we will take a closer look at the idea of ``an extension that would take us beyond
the prospects of a pure theory of Parthood to deliver a theory of parts and wholes'' @{cite "casati_parts_1999"} p.   *}

section {* Theories *}

subsection {* Ground Topology *}

text {* Ground Topology (T) introduces Connectedness (C) as  a primitive relation (just like the 
Parthood relation in Mereology) between individuals. It is assumed to be both reflexive and symmetric 
but not transitive" @{cite "casati_parts_1999"}, p. 52. *}

text {* By connection here we mean a physical type of contact between two individuals. For example my
 hand is connected to my body and India is connected to Pakistan. *} 

locale T =
 fixes C :: "i ⇒ i ⇒ bool" ("C")--"connectedness"
 assumes connection_reflexivity: "C x x" -- "reflexivity of connectedness "
 and connection_symmetry: "C x y ⟶ C y x" -- "symmetry of connectedness"

begin

text {* By saying x is enclosed in y, we mean that if anything is connected to x then that thing will 
also be connected to y. For example my stomach is enclosed in my body since everything that is connected
to my stomach, is also connected to my body. *}

definition E :: "i ⇒ i ⇒ bool" ("E") --"Enclosure"
  where "E x y ≡ ∀z. C z x ⟶ C z y"

text {* The Enclosure relation is reflexive and transitive but not symmetric. *}

lemma enclosure_reflexivity: "E x x" 
  by (simp add: E_def)

lemma enclosure_transitivity: "E x y ⟶ E y z ⟶ E x z "
  by (simp add: E_def)

text {* We assume here that the relation of connectedness is "extensional". By the term "extensional"
we mean that if two things are connected to all of the same things, then they are identical, viz: *}

lemma connection_extensional: "(∀ z. C x z ⟷ C y z) ⟷ x = y" nitpick oops

text {* But that is not a theorem in "T"- nitpick finds a counterexample here. *} 

text {* According to Casati and Varzi, ``If C is extensional then E is also antisymmetric relation'' @{cite "casati_parts_1999"} p.53. *}

lemma
  assumes connection_extensional: "(∀ z. C x z ⟷ C y z) ⟷ x = y"
  shows enclousre_antisymmetry: "E x y ∧ E y x ⟶ x = y"
  using E_def connection_extensional connection_symmetry by blast

text {* As we can see by assuming C is extensional, we get the antisymmetry of the enclosure relation right. *} 

end

subsection{* Ground Mereotopology *}

text{* Ground Mereotopology (MT) involves the connection between Mereology and Topology. The axiom 
of monotonicity tells us that if "x is part of y" then "x is always enclosed in y". That seems obvious
from what I have mentioned about the enclosure relation before. So we can assume this here and we 
call this the ``monotonicity'' axiom. *}

locale MT = ground_mereology + T +
  assumes monotonicity: "P x y ⟶ E x y"

begin

text {* The following theorem could be used as an alternative axiom to monotonicity @{cite "casati_parts_1999"} p. 54: *}

lemma "P x y ⟶ (∀z. C x z ⟶ C z y)"
  using E_def monotonicity connection_symmetry by blast

text {* If x is part of y then x is enclosed in y, according to the monotonicity axiom. If x is enclosed 
in y then everything that is connected to x will also be connected to y, according to the definition
of the enclosure relation. *}

lemma connection_extensional: "(∀ z. C x z ⟷ C y z) ⟷ x = y" nitpick oops

  text {* Monotonicity implies that the mereological overlap is a form of connection; if x and y overlap
then they are also connected. *}

lemma overlap_implies_connection: "O x y ⟶ C x y"
  using E_def monotonicity O_def connection_symmetry connection_reflexivity by blast

text {* But the converse fails. *}

lemma  "C x y ⟶ O x y" nitpick oops

text {* This leads us to define external connection, where x is externally connected to y only 
when x and y are connected but they do not have a common part or they do not overlap. *}

definition EC :: "i => i⇒ bool" ("EC") -- "external connection"
  where "EC x y ≡ C x y ∧ D x y"

text {* On the intended interpretation, this relation holds between things that barely "touch" or
"abut" each other. It is symmetric and irreflexive, but not transitive.  *} 

lemma external_connection_irreflexive: "¬ EC x x"
  by (simp add: EC_def D_irreflexive)

lemma external_connection_symmetric: "EC x y ⟶ EC y x"
  using EC_def connection_symmetry D_symmetry by blast

lemma external_connection_transitive: "EC x y ⟶ EC y z ⟶ EC x z" nitpick [user_axioms] oops

text{* ``Further mereotopological predicates can be defined as follows'' @{cite "casati_parts_1999"} p. 55. *}

definition IP :: "i => i⇒ bool" ("IP") -- "internal part -- part of y connected only to overlappers of y"
  where
"IP x y ≡ P x y ∧ (∀z. C z x ⟶ O z y)"

text {* For example, Ethiopia is an internal part of Africa because every country connected to
Ethiopia overlaps Africa. But Egypt is not an internal part of Africa, because Egypt is connected
to Israel, and Israel does not overlap Africa. *}

text {* Internal parthood is neither reflexive nor irreflexive, but it is antisymmetric and transitive:
 *}

lemma internal_part_reflexive: "IP x x" nitpick [user_axioms] oops

lemma internal_part_irreflexive: "¬ IP x x" nitpick [user_axioms] oops

lemma internal_part_antisymmetry: "IP x y ⟶ IP y x ⟶ x = y"
  by (simp add: IP_def P_antisymmetry)

lemma internal_part_transitivity: "IP x y ⟶ IP y z ⟶ IP x z"
  using IP_def P_transitivity overlap_implies_connection by blast

definition TP :: "i ⇒ i ⇒ bool" ("TP") -- "Tangential part -- part but not internal part"
  where "TP x y ≡ P x y ∧ ¬ IP x y"

text {* As long as something has a tangential part, it is a tangential part of itself: *}

lemma tangential_part_reflexivity: "∃ y. TP y x ⟶ TP x x" by simp

text {* Likewise, tangential parthood is antisymmetric, but not transitive: *}

lemma tangential_part_antisymmetry: "TP x y ⟶ TP y x ⟶ x = y"
  by (simp add: P_antisymmetry TP_def)

lemma tangential_part_transitivity: "TP x y ⟶ TP y z ⟶ TP x z" nitpick [user_axioms] oops

definition IO :: "i ⇒ i ⇒ bool" ("IO") -- "Internal overlap"
  where
"IO x y ≡ ∃ z. IP z x ∧ IP z y"

text {* If x and y overlap internally, there exist a thing which is an internal part of x as well as  
of y. *}

text {* Internal overlap is both reflexive and symmetric; but not transitive. *}

lemma IO_reflexivity: "∃ y. IO y x ⟶ IO x x"
  by simp
lemma IO_symmetric: "IO x y ⟶ IO y x"
  using IO_def by blast
lemma IO_transitive: "IO x y ⟶ IO y z ⟶ IO x z" nitpick [user_axioms] oops

definition TO :: "i ⇒ i ⇒ bool" ("TO") -- "Tangential overlap -- overlap but not internal overlap"
  where
"TO x y ≡ O x y ∧ ¬IO x y"

lemma TO_reflexivity: "∃ y. TO y x ⟶ TO x x"
  by simp
lemma TO_symmetric: "TO x y ⟶ TO y x"
  using IO_symmetric TO_def O_symmetry by blast

definition IU :: "i⇒i⇒ bool" ("IU") -- "Internal underlap"
  where "IU x y ≡ ∃z. IP x z ∧ IP y z"

definition TU :: "i⇒i⇒bool" ("TU") -- "Tangentially underlap"
  where "TU x y ≡ U x y ∧ ¬ IU x y"

text{* ``More generally, For each mereological predicate R we can define corresponding
 mereotopological predicates replacing IR and TR by substituting IP and TP (respectively)
for each occurrence of P in the definiens'' @{cite "casati_parts_1999" } P-55,4.2. For example: *}

definition IPP :: "i => i⇒ bool" ("IPP") -- "Internal proper part"
  where "IPP x y ≡ IP x y ∧ ¬(IP y x)"

definition TPP :: "i⇒i⇒bool" ("TPP") -- "Tangential proper part"
  where
"TPP x y ≡ TP x y ∧ ¬( TP y x)"

text{* Below we define the predicate for self connectedness that makes the difference between solid
wholes (such as table or a cup) and scattered wholes (such as a bikini or a broken glass; to define self-
connectedness we say that x is self-connected if and only if any two parts that make the whole of x are connected
to each other: *}

definition SC :: "i ⇒ bool" ("SC") -- "Self-connectedness"
  where
"SC x ≡ ∀ y.∀ z.(∀ w. O w x ⟷ O w y ∨ O w z) ⟶ C y z"

text {* This definition basically says that x is self-connected if and only if if x is a fusion of y and z,
then y and z are connected. *}

end 

section {* Closed Mereotopology *}

locale CMT = closure_mereology + MT +
  assumes connection_implies_underlap: "C x y ⟶ U x y "

text {* Casati and Varzi say we get the following theorem @{cite "casati_parts_1999"} p. 58. And
we should. If x and y are connected, then according to the axiom they underlap. So then according to
sum closure they have a sum. And since x and y are connected, and self-connected, it seems as if this
sum should be self-connected too: *}

lemma (in CMT) SCC: "(C x y ∧ SC x ∧ SC y) ⟶ (∃z. SC z ∧ (∀ w. O w z ⟷ O w x ∨ O w y))" nitpick [user_axioms] oops

text {* The failure of SCC in Closed Minimal Mereotopology seems to be a minor error in Casati and Varzi. *}
  
locale CEMT = closed_extensional_mereology + CMT

section {* Classical Extensional Mereotopology *}

locale GEMT = classical_extensional_mereology + MT

begin

text {* The problem with Casati and Varzi's parts began to arise when we realized that the only certainty
 about the connectedness relation is that they underlap. Since we have a universal entity which
 underlaps everything, this axiom does not seem to imply anything. Although one of the main aims
 of Mereotopological theory is to tell exactly what difference should be kept between the relation
 of connection and overlap or how should they vary, I don't see the connection axiom taking us  
 anywhere. *}

lemma C_implies_U: "C x y ⟶ U x y"
  by (simp add: universal_underlap)

text {* As we have assumed the existence of the Universal entity which includes everything, it becomes
true that everything is an internal part of the universe: *}

lemma "∀ x. IP x u"
  by (simp add: IP_def P_implies_O u_character)

text {* Now in GEMT, The definition of self connected is itself simpler -- x is self connected means that
every two entities x can be divided into a sum of are connected. *}

lemma SC_def2:  "SC x ⟷ (∀ y z. x = (y ⊕ z) ⟶ C y z)"
proof
  assume "SC x"
  hence "∀ y z. (∀ w. O w x ⟷ (O w y ∨ O w z)) ⟶ C y z"
    using SC_def by simp
  thus "(∀ y z. x = (y ⊕ z) ⟶ C y z)"
    using sum_character by simp
next
  assume "∀ y z. x = (y ⊕ z) ⟶ C y z"
  have "∀ y z. (∀ w. O w x ⟷ (O w y ∨ O w z)) ⟶ C y z"
  proof fix y
    show "∀ z. (∀ w. O w x ⟷ (O w y ∨ O w z)) ⟶ C y z"
    proof fix z
      show "(∀ w. O w x ⟷ (O w y ∨ O w z)) ⟶ C y z"
      proof
        assume "∀ w. O w x ⟷ (O w y ∨ O w z)"
        with sum_intro have "(y ⊕ z) = x"..
        thus "C y z" using ‹∀y z. x = y ⊕ z ⟶ C y z› by blast
      qed
    qed
  qed
  thus "SC x" using SC_def by simp
qed

text {* If two self-connected entities are connected then the sum of them will also be self-connected *}

lemma connected_self_connected_sum: "(C x y ∧ SC x ∧ SC y) ⟶ SC (x ⊕ y)"
proof
  assume "C x y ∧ SC x ∧ SC y"
  have "∀ v w. (x ⊕ y) = (v ⊕ w) ⟶ C v w"
  proof
    fix v
    show "∀ w. (x ⊕ y) = (v ⊕ w) ⟶ C v w"
    proof
      fix w
      show "(x ⊕ y) = (v ⊕ w) ⟶ C v w"
      proof
        assume "(x ⊕ y) = (v ⊕ w)"
        show "C v w"
        proof (cases)
          assume "O v x ∧ O w x ∨ O v y ∧ O w y"
          thus "C v w"
          proof (rule disjE)
            assume "O v x ∧ O w x"
            hence "P x (v ⊕ w) ⟶  x = ((x ⊗ v) ⊕ (x ⊗ w))"
              by (simp add: ‹O v x ∧ O w x› O_symmetry part_of_sum_is_sum_of_products)
            have "P x (v ⊕ w)"
              by (metis ‹x ⊕ y = v ⊕ w› first_summand_inclusion)
            hence "x = ((x ⊗ v) ⊕ (x ⊗ w))"
              using ‹x ≼ v ⊕ w ⟶ x = x ⊗ v ⊕ x ⊗ w› by auto
            hence "C (x ⊗ v) (x ⊗ w)"
              using SC_def2 ‹C x y ∧ SC x ∧ SC y› by blast
            hence "C v (x ⊗ w)"
              by (metis in_first_factor E_def ‹O v x ∧ O w x› connection_symmetry monotonicity product_commutative)
            thus "C v w"
              by (metis in_first_factor E_def ‹O v x ∧ O w x› monotonicity product_commutative)
          next
            assume "O v y ∧ O w y"
            hence "P y (v ⊕ w) ⟶  y = ((y ⊗ v) ⊕ (y ⊗ w))"
              by (simp add: ‹O v y ∧ O w y› O_symmetry part_of_sum_is_sum_of_products)
            have "P y (v ⊕ w)"
              by (metis ‹x ⊕ y = v ⊕ w› second_summand_inclusion)
            hence "y = ((y ⊗ v) ⊕ (y ⊗ w))"
              using ‹y ≼ v ⊕ w ⟶ y = y ⊗ v ⊕ y ⊗ w› by auto
            hence "C (y ⊗ v) (y ⊗ w)"
              using SC_def2 ‹C x y ∧ SC x ∧ SC y› by blast
            hence "C v (y ⊗ w)"
              by (metis E_def in_first_factor ‹O v y ∧ O w y› connection_symmetry monotonicity product_commutative)
            thus "C v w"
              by (metis E_def in_first_factor ‹O v y ∧ O w y› monotonicity product_commutative)
          qed
        next
          assume "¬ (O v x ∧ O w x ∨ O v y ∧ O w y)"
          hence "x = w ∧ y = v ∨ x = v ∧ y = w"
            using disjoint_summand_identity ‹x ⊕ y = v ⊕ w›
            by (metis D_def P_implies_O sum_commutative second_summand_inclusion summand_part)
          thus "C v w"
            using ‹C x y ∧ SC x ∧ SC y› connection_symmetry by blast
        qed
      qed
    qed
  qed
  thus "SC (x ⊕ y)" using SC_def2 by simp
qed

text {* Another way of stating the above lemma is that if two self connected entities are connected then
there is a connected entity which exactly overlaps them: *}

lemma "(C x y ∧ SC x ∧ SC y) ⟶ (∃ z. SC z ∧ (∀ w. O w z ⟷ O w x ∨ O w y))"
proof
  assume "(C x y ∧ SC x ∧ SC y)"
  with connected_self_connected_sum have "SC (x ⊕ y)"..
  have "∀ w. O w (x ⊕ y) ⟷ O w x ∨ O w y" using sum_character.
  hence "SC (x ⊕ y) ∧ (∀ w. O w (x ⊕ y) ⟷ O w x ∨ O w y)" 
    using ‹SC (x ⊕ y)› by simp
  thus "∃ z. SC z ∧ (∀ w. O w z ⟷ O w x ∨ O w y)"
    by blast
qed

text {* Below are some theorems and lemmas which we had to prove for our own convenience to understand
exactly the concept of definite descriptions used for the operators like sum, product, interior, 
exterior, and to prove a few more things from them. *}

lemma sum_parts : "∃z. P z (x ⊕ y) ⟶ P z x ∨ P z y"
  using ground_mereology.P_reflexivity ground_mereology_axioms by blast

lemma separation: "O x y ⟶ O x z ⟶ (P x (y ⊕ z) ⟶ ((x ⊗ y) ⊕ (x ⊗ z)) = x)" 
  by (simp add: part_of_sum_is_sum_of_products)

lemma identity1 : "((D v x ∧  D v y) ∧ x ⊕ y = w ⊕ v ∧ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y))⟶ w = x ⊕ y"
proof
  assume "(D v x ∧  D v y) ∧ x ⊕ y = w ⊕ v ∧ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y)"
  hence "∀z. O z x ∨ O z y ⟷ O z w ∨ O z v"
    by (metis sum_character)
  hence "∃z. O z x ∧ ¬ O z y ∨ ¬ O z v"
    using ‹(D v x ∧ D v y) ∧ x ⊕ y = w ⊕ v ∧ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y)› by blast
  hence "w = x ⊕ y"
    using D_def ‹(D v x ∧ D v y) ∧ x ⊕ y = w ⊕ v ∧ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y)› ‹∀z. (O z x ∨ O z y) = (O z w ∨ O z v)› ground_mereology.O_reflexivity ground_mereology_axioms by blast
  thus "w = x ⊕ y" 
    by blast
qed

lemma identity2 : "((D w x ∧ D w y) ∧ x ⊕ y = w ⊕ v ∧ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y))⟶ v = x ⊕ y"
  using GEMT.identity1 GEMT_axioms mereology.sum_commutative by fastforce

lemma identity3 : "((D v x ∧ D w y) ∧ x ⊕ y = w ⊕ v ∧  ¬ (O v x ∧ O w x ∨ O v y ∧ O w y))⟶ x = w ∧ y = v"
  using disjoint_summand_identity sum_commutative by fastforce

lemma identity4 : "((D w x ∧ D v y) ∧ x ⊕ y = w ⊕ v ∧  ¬ (O v x ∧ O w x ∨ O v y ∧ O w y))⟶ w = y ∧ v = x"
  by (metis GEMT.identity3 GEMT_axioms mereology.sum_commutative)

lemma identity: "x ⊕ y = w ⊕ v ⟶ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y) ⟶ x = w ∧ y = v ∨ x = v ∧ y = w" 
proof 
  assume i1 : "x ⊕ y = w ⊕ v"
  show "¬ (O v x ∧ O w x ∨ O v y ∧ O w y) ⟶ x = w ∧ y = v ∨ x = v ∧ y = w"
  proof
    assume i2 :  "¬ (O v x ∧ O w x ∨ O v y ∧ O w y)"
      from i1 and i2 have "x ⊕ y = w ⊕ v ∧ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y)" by blast
      hence "∀z. O z x ∨ O z y ⟷ O z w ∨ O z v"
        by (metis sum_character)
      hence I1 : "D v x ∨ D w x ∧ D v y ∨ D w y"
        using D_def i2 by auto
      hence I2 : "(D v x ∧ D v y) ∨ (D v x ∧ D w y) ∨ (D w x ∧ D v y) ∨ (D w x ∧ D w y)"
        using D_def i2 by blast
      hence "(w = x ⊕ y) ∨ (v = x ⊕ y) ∨ (w = y ∧ v = x) ∨ (x = w ∧ y = v)"
        by (smt GEMT.identity1 GEMT_axioms ‹x ⊕ y = w ⊕ v ∧ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y)› identity2 identity3 identity4)
      hence "x = w ∧ y = v ∨ x = v ∧ y = w"
        by (metis D_def ‹∀z. (O z x ∨ O z y) = (O z w ∨ O z v)› ‹x ⊕ y = w ⊕ v ∧ ¬ (O v x ∧ O w x ∨ O v y ∧ O w y)› disjoint_summand_identity ground_mereology.O_reflexivity ground_mereology_axioms sum_commutative)
      thus "x = w ∧ y = v ∨ x = v ∧ y = w" 
        by blast
    qed
  qed

definition i :: "(i ⇒ i)" ("❙i")--"interior"
  where "❙i x ≡ σ z. IP z x"

text {* The interior of x is the thing which consists of all and only the internal parts of x. *}

definition e :: "(i⇒i)" ("e") -- "exterior"
  where "e x ≡ ❙i (─ x)"

text {* The exterior of x is the thing which consists of all and only the internal parts of the complement
of x. (A thing is a part of the complement of x if and only if it does not overlap x). *}

definition c :: "i⇒i" ("c")--"closure"
  where
"c x ≡ ─ (e x)"

text {* The closure of x is the complement of exterior of x. *}

definition b :: "i⇒i" ("b")--"boundary"
  where "b x ≡ ─ (❙i x ⊕ e x)"

text {* The boundary of x is consisting everything that is neither in the interior of x nor in the 
exterior of x. *} 

text{* These integrated operators are partially defined, unless we assume the existence of a null 
individual that is part of everything *}

text {* We should note that a boundary has no interior and the universe has no exterior. *}  

text {* We noticed with Isabelle/HOL that to prove anything much stated using a definite description we
first must prove that the individual denoted by the description in fact meets that description. *}  

lemma interior_fusion: "(∃ y. IP y x) ⟶ (∃ v. ∀ y. O y v ⟷ (∃ z. IP z x ∧ O z y))" using fusion.

lemma interior_intro: "(∀ y. O y a ⟷ (∃ z. IP z x ∧ O z y)) ⟶ (❙i x) = a"
proof -
  have "(∀ y. O y a ⟷ (∃ z. IP z x ∧ O z y)) ⟶ (σ z. IP z x) = a" using fusion_intro.
  thus ?thesis using i_def by simp
qed

lemma interior_character: "(∃ y. IP y x) ⟶ (∀ y. O y (❙i x) ⟷ (∃ z. IP z x ∧ O z y))"
proof
  assume antecedent: "(∃ y. IP y x)"
  with interior_fusion have "∃ v. ∀ y. O y v ⟷ (∃ z. IP z x ∧ O z y)"..
  then obtain v where v: "∀ y. O y v ⟷ (∃ z. IP z x ∧ O z y)"..
  with interior_intro have "(❙i x) = v"..
  thus "(∀ y. O y (❙i x) ⟷ (∃ z. IP z x ∧ O z y))"
    using v by blast
qed

lemma interior_is_part: "(∃ y. IP y x) ⟶ P (❙i x) x" -- "the interior of an individual is part of it"
proof
  assume "(∃ y. IP y x)"
  with interior_fusion have "∃ v. ∀ y. O y v ⟷ (∃ z. IP z x ∧ O z y)"..
  then obtain a where a: "∀ y. O y a ⟷ (∃ z. IP z x ∧ O z y)"..
  with interior_intro have "(❙i x) = a"..
  thus "P (❙i x) x"
    by (metis IP_def P_iff_all_O_O a O_symmetry)
qed

lemma interior_overlaps: "(∃ y. IP y x) ⟶ O (❙i x) x"
  by (simp add: P_implies_O interior_is_part)
lemma interior_connects:  "(∃ y. IP y x) ⟶ C (❙i x) x"
  using P_implies_O interior_is_part overlap_implies_connection by blast
lemma encloses_interior:  "(∃ y. IP y x) ⟶ E (❙i x) x"
  by (simp add: interior_is_part monotonicity)

lemma exterior_closure: "(∃ y. IP y (─ x)) ⟶ (∃ a. ∀ y. O y a ⟷ (∃ z. IP z (─ x) ∧ O z y))"
  by (simp add: interior_fusion) 

lemma exterior_intro: "(∀ y. O y a ⟷ (∃ z. IP z (─ x) ∧ O z y)) ⟶ (e x) = a"
proof
  assume "(∀ y. O y a ⟷ (∃ z. IP z (─ x) ∧ O z y))"
  with interior_intro have "(❙i (─ x)) = a"..
  thus "(e x) = a"
    using e_def by simp
qed

lemma exterior_character: "(∃ y. IP y (─ x)) ⟶ (∀ y. O y (e x) ⟷ (∃ z. IP z (─ x) ∧ O z y))" 
  by (simp add: e_def interior_character)

lemma "x ≠ u ∧ (∃ y. IP y (─ x)) ⟶ ¬ P (e x) x" --"external of x is not part of x"
  using e_def P_implies_O in_comp_iff_disjoint interior_is_part D_def by fastforce

lemma "x ≠ u ∧ (∃ y. IP y (─ x)) ⟶ ¬ P x (e x)" --" x is also not part of external of x"
  by (metis e_def P_implies_O P_iff_all_O_O complements_disjoint interior_is_part D_def)

lemma "x ≠ u ∧ (∃ y. IP y (─ x)) ⟶ D x (e x)" --" even x and external of x never ever overlap"
  using D_symmetry complement_character e_def interior_is_part by fastforce

text  {* Since the closure of x is the complement of exterior of x, a thing is a part of the closure of x if and
only if that thing does not overlap the exterior of x. *}

lemma closure_intro:  "(∀ y. P y a ⟷ D y (e x)) ⟶ (c x) = a"
  by (metis D_irreflexive P_antisymmetry P_iff_all_D_D P_reflexivity c_def e_def in_comp_iff_disjoint u_character)

lemma closure_character: "x ≠ u ∧ (∃ y. IP y (─ x)) ⟶ (∀ y. P y (c x) ⟷ D y (e x))"
proof
  assume "x ≠ u ∧ (∃y. IP y (─ x))"
    have "∀y. P y (c x) ⟷ D y (e x)"
      by (metis D_def P_implies_O ‹x ≠ u ∧ (∃y. IP y (─ x))› additive_inverse c_def complements_disjoint e_def in_comp_iff_disjoint interior_is_part summand_inclusion)
    hence "∀y. P y (c x) ⟷ D y (e x)"
      by blast
    thus "(∀ y. P y (c x) ⟷ D y (e x))"
      by blast
  qed

  text {* The closure of x contains everything that is not overlapping with the interior of all the things that
do not overlap x *}

lemma closure_closure: "x ≠ u ∧ (∃ y. IP y (─ x)) ⟶ (∃ a. ∀ y. P y a ⟷ D y (e x))"
proof
  assume antecedent: "x ≠ u ∧ (∃ y. IP y (─ x))"
  with closure_character have "(∀ y. P y (c x) ⟷ D y (e x))"..
  thus "(∃ a. ∀ y. P y a ⟷ D y (e x))"..
qed

lemma closure_inclusion: "x ≠ u ∧ (∃ y. IP y (─ x)) ⟶ P x (c x)"--"x is part of closure of x"
  using closure_character D_symmetry e_def in_comp_iff_disjoint interior_is_part by fastforce

lemma closure_overlap: "x ≠ u ∧ (∃ y. IP y (─ x)) ⟶ O x (c x)"--"x and closure of x overlap"
  by (simp add: P_implies_O closure_inclusion)

lemma closure_connection: "x ≠ u ∧ (∃ y. IP y (─ x)) ⟶ C x (c x)"
  by (simp add: closure_overlap overlap_implies_connection)

lemma boundary_closure: "(❙i x ⊕ e x) ≠ u ⟶ x ≠ u ⟶ (∃ z. IP z x) ⟶ (∃ z. IP z (─ x))⟶
 (∃ a. ∀ z. P z a ⟷ D z (❙i x ⊕ e x))" 
  using unique_complement by blast

text {* As defined; the boundary of x is the complement of the sum of the interior and exterior of x, every 
part of the boundary of x is disjoint with the interior of x and as well as with the exterior of x. *}

lemma boundary_intro : "(∀ w. P w a ⟷ D w (❙i x ⊕ e x)) ⟶ b x = a"
  by (metis D_def P_antisymmetry P_implies_O P_reflexivity b_def in_comp_iff_disjoint u_character) 

lemma boundary_character: "(❙i x ⊕ e x) ≠ u ⟶ x ≠ u ⟶ (∃ z. IP z x) ⟶ (∃ z. IP z (─ x)) ⟶
 (∀ z. P z (b x) ⟷ D z (❙i x ⊕ e x))"
  by (simp add: b_def in_comp_iff_disjoint)  

text {* In Varzi's "Parts, Wholes and Part-Whole Relations: The Prospects of Mereotopology", Two
different kinds of entities are defined: one is said to be open and the other one is said to be closed. *}

text {* Open entities are said to be the ones which are identical to their interior; x is the entity containing 
all and only the internal parts of x. *}

definition OP :: "i ⇒ bool" ("OP")--"open"
  where "OP x ≡ ❙i x = x"

text {* On the other hand, closed entities are defined as the ones which are identical to their closure. *}

definition CL :: "i ⇒ bool" ("CL") -- "closed"
  where "CL x ≡ c x = x"

end

text{* According to Casati and Varzi ``we can get closer to standard topological theories by supplementing the axiom
of symmetry and reflexivity and the monotonicity of connectedness, with the mereologized 
analogues of the standard Kuratowski (1922) axioms for topological closure'' @{cite "casati_parts_1999"}, p. 59. *}

text {* The following version of the axioms are from Varzi``Parts, Wholes and Part-Whole Relations: The Prospects
of Mereotopology'' @{cite "varzi_parts_1996"} p. 273: *}

locale GEMTC = GEMT + 
  assumes C4: "CL x ∧ CL y ⟶ CL (x ⊕ y)" 
  assumes C5: "(∀ x. F x ⟶ Cl x) ⟶ (∃ z. ∀ y. F y ⟶ z ≼ y) ⟶ CL (π z. F z)"

begin

text {* The interior of x is always a part of x. *}

lemma interior_inclusion : "∃ y. IP y x ⟶ P (❙i x) x"
  by (simp add: IP_def)

text {* Interior of interior x is interior of x. *}

lemma interior_idempotence: "∃ y. IP y x ⟶ ❙i (❙i x) = ❙i x"
  by (metis IP_def P_iff_all_O_O interior_character internal_part_antisymmetry O_reflexivity)

text {* The theorem that interior distributes over product is claimed to follow in Casati and Varzi
@{cite "casati_parts_1999"} p. 59; but when I went to prove that I couldn't do it. There might be an error
here but it's probably something I'm missing in the proof so I will just use it as an axiom. *}

lemma interior_distributes_over_product: 
 "(∃ z. IP z (x ⊗ y)) ∧ (∃ z. IP z x) ∧ (∃ z. IP z y) ⟶ ❙i (x ⊗ y) = ❙i x ⊗ ❙i y " sorry

text {* The intersection or the product of two open entities will also be an open entity. *}

lemma C4': "OP x ∧ OP y ∧ (∃ z. IP z (x ⊗ y)) ∧ (∃ z. IP z x) ∧ (∃ z. IP z y) ⟶ z = x ⊗ y ⟶ OP z" 
proof
  assume "OP x ∧ OP y ∧ (∃ z. IP z (x ⊗ y)) ∧ (∃ z. IP z x) ∧ (∃ z. IP z y)"
  show "z = x ⊗ y ⟶ OP z"
  proof 
    assume "z = x ⊗ y"
    with  interior_distributes_over_product have "❙i x ⊗ ❙i y = ❙i (x ⊗ y)"
      by (simp add: ‹OP x ∧ OP y ∧ (∃z. IP z (x ⊗ y)) ∧ (∃z. IP z x) ∧ (∃z. IP z y)›)
    hence "❙i x ⊗ ❙i y = x ⊗ y"
      using GEMT.OP_def GEMT_axioms ‹OP x ∧ OP y ∧ (∃z. IP z (x ⊗ y)) ∧ (∃z. IP z x) ∧ (∃z. IP z y)› by auto
    hence "x ⊗ y = ❙i (x ⊗ y)"
      using ‹❙i x ⊗ ❙i y = ❙i (x ⊗ y)› by auto
    hence " OP (x ⊗ y)"
      using GEMT.OP_def GEMT_axioms by auto
    thus  "OP z "
      by (simp add: ‹z = x ⊗ y›)
  qed
qed

text {* If there is an entity which have only those parts which are parts of both the interior of x
and interior of y, then that entity is the product of the interior of x and the interior of y. *}

lemma p_intro : "(∀z. P a z ⟷ (P z (❙i x) ∧ P z (❙i y))) ⟶ ((❙i x) ⊗ (❙i y)) = a"
  by (metis (full_types) P_antisymmetry P_implies_O complements_disjoint D_def universe_closure u_intro)

text {* Below is just one simple lemma about the product -- if everything a is part of is part of x and y,
then a is the product of x and y. *}

lemma p : "(∀z. P a z ⟷ (P z x ∧ P z y)) ⟶ (x ⊗ y) = a"
  by (metis P_antisymmetry P_implies_O D_def in_comp_iff_disjoint universe_closure)

text {* If there is an entity with an internal part, then if everything that entity is part of 
is part of x and y then that entity is the interior of the product of x and y. *}

lemma pi : "(∃w. IP a w ∧ (∀v. P w v ⟷ P v x ∧ P v y) ⟶ a = ❙i (x ⊗ y))"
  by (meson P_antisymmetry P_reflexivity)

text {* There is a thing such that if (x ⊗ y) is an internal part of it, then it is part of x and y. *}

lemma Pi3 : "∃w. IP (x ⊗ y) w ⟶ P w x ∧ P w y"
  using IP_def by blast

text {* The interior of (x ⊗ y) is part of (x ⊗ y). *}

lemma pp : "(∃z. IP z (x ⊗ y)) ⟶ P (❙i (x ⊗ y)) (x ⊗ y)"
  using interior_is_part by auto

text {* One stronger theorem for the connectedness relation is mentioned here -- x and y are connected 
if and only if they either overlap or are externally connected. *}  

lemma  C_iff_O_orEC: "C x y ⟷ (O x y ∨ EC x y)"
  using EC_def D_def overlap_implies_connection by blast

text {* Casati and Varzi say two things are externally connected if and only if they share only a 
boundary. They write two things are connected if and only if, either one's closure overlaps the 
 other entity or they overlap. 
And they also say if x and y are externally connected then they are connected but their interiors 
are not.  *}

text {* In their words, ``two things are(externally) connected if and only if they share (only) a boundary,i.e.,if and 
only if the closure of one overlaps the other, or vice versa:'' @{cite "casati_parts_1999"}'p.59. *} 

text {* But we haven't been able to prove that: *}

lemma EC_implies_O_c: "x ≠ u ⟶ (∃ z. IP z (─ x)) ⟶ y ≠ u ⟶ (∃ z. IP z (─ y)) ⟶ 
EC x y ⟶ (O x (c y) ∨ O (c x) y)"
proof 
  assume x_isnt_u: "x ≠ u"
  with complement_character have comp_x: "∀ w. (w ≼ ─ x) ⟷ D w x"..
  show "(∃ z. IP z (─ x)) ⟶ y ≠ u ⟶ (∃ z. IP z (─ y)) ⟶  EC x y ⟶ (O x (c y) ∨ O (c x) y)"
  proof
    assume IP_comp_x: "(∃ z. IP z (─ x))"
    with exterior_character have ext_x: "(∀ y. O y (e x) ⟷ (∃ z. IP z (─ x) ∧ O z y))"..
    from x_isnt_u and IP_comp_x have "x ≠ u ∧ (∃ z. IP z (─ x))"..
    with closure_character have cl_x: "(∀ y. (y ≼ c x) ⟷ D y (e x))"..
    show "y ≠ u ⟶ (∃ z. IP z (─ y)) ⟶ EC x y ⟶ (O x (c y) ∨ O (c x) y)"
    proof
      assume y_isnt_u: "y ≠ u"
      with complement_character have comp_y: "∀ w. (w ≼ ─ y) ⟷ D w y"..
      show "(∃ z. IP z (─ y)) ⟶  EC x y ⟶ (O x (c y) ∨ O (c x) y)"
      proof
        assume IP_comp_y: "(∃ z. IP z (─ y))"
        with exterior_character have ext_y: "(∀ v. O v (e y) ⟷ (∃ z. IP z (─ y) ∧ O z v))"..
        from y_isnt_u and IP_comp_y have "y ≠ u ∧ (∃ z. IP z (─ y))"..
        with closure_character have cl_y: "(∀ v. (v ≼ c y) ⟷ D v (e y))"..
        show "EC x y ⟶ (O x (c y) ∨ O (c x) y)"
        proof
          assume "EC x y"
          hence "D x y"
            using EC_def by simp
          hence "y ≼ ─ x" using comp_x
            using D_symmetry by blast
          thus "(O x (c y) ∨ O (c x) y)" using comp_x ext_x cl_x comp_y ext_y cl_y sorry
        qed
      qed
    qed
  qed
qed

lemma "x ≠ u ⟶ (∃ z. IP z (─ x)) ⟶ y ≠ u ⟶ (∃ z. IP z (─ y)) ⟶
C x y ⟷ (O x y ∨ (O x (c y) ∨ O (c x) y))"
proof 
  assume x_isnt_u: "x ≠ u"
  with complement_character have comp_x: "∀ w. (w ≼ ─ x) ⟷ D w x"..
  show "(∃ z. IP z (─ x)) ⟶ y ≠ u ⟶ (∃ z. IP z (─ y)) ⟶ C x y ⟷ (O x y ∨ (O x (c y) ∨ O (c x) y))"
  proof
    assume IP_comp_x: "(∃ z. IP z (─ x))"
    with exterior_character have ext_x: "(∀ y. O y (e x) ⟷ (∃ z. IP z (─ x) ∧ O z y))"..
    from x_isnt_u and IP_comp_x have "x ≠ u ∧ (∃ z. IP z (─ x))"..
    with closure_character have cl_x: "(∀ y. (y ≼ c x) ⟷ D y (e x))"..
    show "y ≠ u ⟶ (∃ z. IP z (─ y)) ⟶ C x y ⟷ (O x y ∨ (O x (c y) ∨ O (c x) y))"
    proof
      assume y_isnt_u: "y ≠ u"
      with complement_character have comp_y: "∀ w. (w ≼ ─ y) ⟷ D w y"..
      show "(∃ z. IP z (─ y)) ⟶ C x y ⟷ (O x y ∨ (O x (c y) ∨ O (c x) y))"
      proof
        assume IP_comp_y: "(∃ z. IP z (─ y))"
        with exterior_character have ext_y: "(∀ v. O v (e y) ⟷ (∃ z. IP z (─ y) ∧ O z v))"..
        from y_isnt_u and IP_comp_y have "y ≠ u ∧ (∃ z. IP z (─ y))"..
        with closure_character have cl_y: "(∀ v. (v ≼ c y) ⟷ D v (e y))"..
        show "C x y ⟷ (O x y ∨ (O x (c y) ∨ O (c x) y))"
        proof
          assume "C x y"
          show "O x y ∨ (O x (c y) ∨ O (c x) y)"
          proof
            cases
            assume "O x y"
            thus "O x y ∨ (O x (c y) ∨ O (c x) y)"..
          next assume "¬ O x y"
            hence "EC x y" using EC_def ‹C x y› by blast
            hence "(O x (c y) ∨ O (c x) y)"
              using EC_implies_O_c sorry
            thus "(O x y ∨ (O x (c y) ∨ O (c x) y))"..
          qed
        next
          assume "O x y ∨ (O x (c y) ∨ O (c x) y)"
          thus "C x y" 
          proof (rule disjE)
            assume "O x y"
            thus "C x y" by (simp add: overlap_implies_connection)
          next
            assume "(O x (c y) ∨ O (c x) y)"
            thus "C x y"
            proof (rule disjE)
              assume "O x (c y)"
              show "C x y"
              proof cases
                assume "y = u"
                hence "O x y"
                  using y_isnt_u by auto
                thus "C x y" by (simp add: overlap_implies_connection)
              next
                assume "y ≠ u"
                thus "C x y"  sorry
              qed
            next
              assume "O (c x) y"
              show "C x y"
              proof
                cases
                assume "x = u"
                thus "C x y"
                  using x_isnt_u by blast
              next
          assume "x ≠ u"
          thus "C x y"  sorry
        qed
      qed
    qed
  qed
qed
qed
qed
qed

text {* Even after proving a lot of certain things we were still unable to prove these main theorems
in Casati and Varzi @{cite "casati_parts_1999"}. It seems to be a serious error. *}

text {* I think the error occurs because the relation connectedness is not provided with any strong 
enough axiom to prove much about it. We also think the following may be a counterexample; Suppose there
are four simple individuals (a simple or an atom is an individual that has no parts other than itself):
a, b, c and d. Suppose a is connected to b, and c is connected to d, and there are no more connections
amongst the four simples. But suppose also that a + b is connected to c + d. (It follows that all the
other complex (non-simple) individuals are connected as well, but that is not important). It follows that
both a and b are interior parts of a + b, and both c and d are interior parts of c + d, so the interior of
a + b is a + b itself, and the interior of c + d is c + d itself. The exterior of a + b is the interior of its complement, which is c + d. The closure 
of a + b is the complement of its exterior, so that's just a + b. Likewise, the closure of c + d is 
also c + d.*}

text {* It seems to us (but we have not yet verified formally) that this counterexample satisfies all the
axioms of GEMTC, without satisfying the theorems that we could not prove above. *}

end