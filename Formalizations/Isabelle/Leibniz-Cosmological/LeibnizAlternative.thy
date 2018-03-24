theory LeibnizAlternative
imports Main
begin
typedecl μ --"things in the world"
consts moving :: "μ⇒bool"
consts moves :: "μ⇒μ⇒bool"(infix "moves"52)

consts isMoved ::"μ⇒bool"
consts body :: "μ⇒bool"

consts isPartOf :: "μ⇒μ⇒bool"(infix "isPartOf"52)
consts hasInfiniteParts :: "μ⇒bool"  

abbreviation movesTheInfinite :: "μ⇒bool" where
"movesTheInfinite x ≡ ∀y.(hasInfiniteParts y ∧ x moves y)"

text "Leibniz writes: **Infinite power is an original capacity [potentia] to move the infinite. For
 power is the same as original capacity; hence we say that secondary causes operate by virtue[virtus]
 of the primary**"

text "comment: From this definition of infinite power we can infer infinite power is the capacity to
 move the infinite which belongs to some incorporeal "

abbreviation infinitePower :: "μ⇒bool" where
"infinitePower x ≡ movesTheInfinite x"

abbreviation substance :: "μ⇒bool" where
"substance x ≡ moving x ∨ isMoved x"

abbreviation incorporeal :: "μ⇒bool" where
"incorporeal x ≡ ¬body x"

abbreviation God :: "μ⇒bool" where
"God x ≡ incorporeal x ∧ substance x ∧ infinitePower x"

text "comment: The following axiom seems to be a reasonable interpretation of Leibniz´s notion of infinity."

axiomatization where Inf: "hasInfiniteParts y ⟹ x moves y ⟹ movesTheInfinite x"

text "Leibniz's Postulate: **Any number of things whatever maybe taken simultaneously and yet be
 treated as one whole. If anyone makes bold to deny this, I will prove it. The concept of parts is
 this: Given a plurality of beings all of which are understood to have something in common; then,
 since it is inconvenient or impossible to enumerate all of them every time, one name is thought of
 which takes the place of all the parts in our reasoning, to make the expression shorter. This is
 called the whole. But in any number of given things whatever, even infinite, we can understand what
 is true of all, since we can enumerate them all individually, at least in an infinite time. It is
 therefore permissible to use one name in our reasoning in place of all, and that will itself be a whole.**" 

axiomatization where Postulate_a: "∃P. ∀x.∀y. (P x ∧ P y)⟹∃w.∀x.∀y.(x isPartOf w ∧ y isPartOf w)"

text "Leibniz Axioms are interpreted in a straight forward manner"

axiomatization where Axiom1: "isMoved x ⟷ (∃y.(y moves x))"
axiomatization where Axiom2: "∀x.(moving x ∧ body x)⟶ isMoved x"
axiomatization where Axiom3: "∀y.(∀x.(x isPartOf y)∧(isMoved x)⟶ isMoved y)"
axiomatization where Axiom4: "∀x.((body x) ⟶ (hasInfiniteParts x))"
axiomatization where Observation: "∃x.(body x ∧ moving x)"

lemma "∃x. God x" nitpick[user_axioms,verbose] text"(Nitpick found a counterexample)"
  oops

text "However, These are not enough to get to the conclusion Leibniz wants" 

text "comment: To model Leibniz's argument as closely as possible (and to make the argument sound)
 a couple of new axioms are introduced that are plausible in the context of Leibniz argument."


text "comment: First it can be understood easily, if something has infinite parts and yet is a part of
 something else, then it has infinite parts too"

axiomatization where InfinitePartsPart:"∀x.∀y.(((x isPartOf y)∧ hasInfiniteParts x)⟶ hasInfiniteParts y)"

text "comment: It is also indeed an axiom where body is the part of whole and the whole is moved,
 Leibniz clearly stated if the whole is moved we have definitely reached at some incorporeal so this
 can be stated"
axiomatization where NoPartMoves : "body x ∧ x isPartOf y ∧ isMoved y ⟷ ¬(x moves y)"

text"Leibniz writes: **I call substance whatever moves or is moved.** comment: Now finally, we have
 to prove that God is a substance. In this alternative of Leibniz's cosmological proof, we interpreted
 substance as either moving, or is moved. But we can not say God is moved because if that was the case,
 then who moves the God?, Since God has the infinite Power to move the infinite we can infer God can 
 move itself or God is moving."

axiomatization where InfiniteMoves: "infinitePower x ⟶ moving x"

lemma God:"∃x. God x"
proof-
  from Observation have "∃A. (body A ∧ moving A)" by simp
  then obtain A where obtA: "(body A ∧ moving A)" by auto 
  hence "∃y. y moves A" using Axiom1 Axiom2 by auto
  from this have "hasInfiniteParts A" using Axiom4 obtA by auto
  from this have "isMoved A" using ‹∃y. y moves A› using Axiom1 by blast
  hence "∃y. infinitePower y" using ‹∃y. y moves A› ‹hasInfiniteParts A› Inf by blast
  from this have "∃y. infinitePower y ∧ moving y" using InfiniteMoves by blast
  then obtain y where obty:"infinitePower y ∧ moving y" by auto
  from this have "substance y ∧ infinitePower y" by auto
  then have "incorporeal y ∨ body y" by auto
  {
  assume "incorporeal y"
  hence "God y" by (simp add: ‹substance y ∧ infinitePower y›)
  hence "∃x. God x" by auto}

  moreover {
    assume B: "body y"
    have "moving y" using obty by (rule conjunct2)
    hence "isMoved y" using  Axiom2 ‹body y› by auto
    have "isMoved A" using Axiom1 ‹∃y. y moves A› by auto
    hence "isMoved A ∧ isMoved y" using ‹isMoved y› by (rule conjI)
    {
      assume "¬(∃x. God x)"
        from obty B have "isMoved A ∧ isMoved y" using ‹isMoved A ∧ isMoved y› by auto
        from this have "∃C.(isMoved A ∧isMoved y)⟷(A isPartOf C ∧ y isPartOf C)" using Postulate_a by auto
        then obtain C where obtC1: "(isMoved A ∧isMoved y)⟷(A isPartOf C ∧ y isPartOf C)" by auto
        hence "(A isPartOf C ∧ y isPartOf C)"using ‹isMoved A ∧ isMoved y› by auto note this 
        from this have "A isPartOf C ∧ y isPartOf C" using ‹isMoved A ∧ isMoved y› obtC1 by auto
        from this have "(A isPartOf C ∧ y isPartOf C)∧(isMoved A ∧ isMoved y) " using ‹isMoved A ∧ isMoved y› by (rule conjI)
        from this have "A isPartOf C" by auto
        have "isMoved A" using ‹isMoved A ∧ isMoved y› by (rule conjunct1)
        have "A isPartOf C ∧ isMoved A" using ‹A isPartOf C› ‹isMoved A› by (rule conjI) 
        from this have " isMoved C" using Axiom3 by auto
        from this have " ∃G. G moves C" using Axiom1 by simp
        from this obtain G where " G moves C " by auto
        have "body y" using ‹body y› by auto
        have "y isPartOf C" using ‹A isPartOf C ∧ y isPartOf C› by (rule conjunct2)
        have "hasInfiniteParts y" using ‹body y› Axiom4 by blast
        from this have "hasInfiniteParts C" using ‹y isPartOf C› InfinitePartsPart by auto 
        from this have "infinitePower G" using ‹G moves C› Inf by blast
        from this have "substance G" using InfiniteMoves by auto
        have "incorporeal G" using B ‹(A isPartOf C ∧ y isPartOf C) ∧ isMoved A ∧ isMoved y› ‹isMoved C› NoPartMoves obty by blast
        hence "God G" using ‹substance G› ‹infinitePower G› by blast
        hence "False" using ‹¬(∃x. God x)› by blast
      }
      hence "∃x.(God x)" by blast}
    ultimately show "∃x. (God x)" by auto
  qed

end

        

       






  
