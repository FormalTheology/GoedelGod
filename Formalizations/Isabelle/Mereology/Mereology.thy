section {* Introduction *}

theory Mereology
imports "~~/src/HOL/Algebra/Order"
begin

section {* Definitions *}

typedecl "i" -- "the type of individuals"

locale mereology  =
  fixes P:: "i \<Rightarrow> i \<Rightarrow> bool" (infix "\<preceq>" 50) -- "parthood"

begin

definition PP:: "i \<Rightarrow> i \<Rightarrow> bool" (infix "\<prec>" 50) 
  where "x \<prec> y \<equiv> x \<preceq> y \<and> x \<noteq> y" -- "proper parthood"

lemma PP_irreflexivity: "\<not> x \<prec> x"
  by (simp add: PP_def) -- "proper parthood is irreflexive"

definition O:: "i \<Rightarrow> i \<Rightarrow> bool" ("O")
  where "O x y \<equiv> \<exists> z. z \<preceq> x \<and> z \<preceq> y" -- "overlap"

lemma O_symmetry: "O x y \<longrightarrow> O y x"
  using O_def by blast -- "overlap is symmetric"

definition D:: "i \<Rightarrow> i \<Rightarrow> bool" ("D")
  where "D x y \<equiv> \<not> O x y" -- "disjointness"

lemma D_symmetry: "D x y \<longrightarrow> D y x"
  using D_def O_def by auto -- "disjointness is symmetric"

definition U:: "i \<Rightarrow> i \<Rightarrow> bool" ("U")
  where "U x y \<equiv> \<exists> z. x \<preceq> z \<and> y \<preceq> z" -- "underlap"

lemma U_symmetry: "U x y \<longrightarrow> U y x"
  using U_def by auto -- "underlap is symmetric"

definition sum:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<oplus>" 52)
  where "x \<oplus> y \<equiv> THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y" -- "sum or pair fusion"

lemma sum_commutative: "x \<oplus> y = y \<oplus> x" -- "summation is commutative"
proof -
  have "(THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w y) = (THE z. \<forall> w. O w z \<longleftrightarrow> O w y \<or> O w x)"
    by metis
  thus ?thesis
    using sum_def by simp
qed

definition product:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<otimes>" 53)
  where "x \<otimes> y \<equiv> THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> y" -- "product or intersection"

lemma product_commutative: "x \<otimes> y = y \<otimes> x"
proof -
  have  "(THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq>  x \<and> w \<preceq> y) = (THE z. \<forall> w. w \<preceq>  z \<longleftrightarrow> w \<preceq>  y \<and> w \<preceq> x)"
    by metis
  thus ?thesis
    using product_def by simp
qed

definition u:: "i" ("u")
  where "u \<equiv> THE z. \<forall> w. w \<preceq> z" -- "the universe"

definition difference:: "i \<Rightarrow> i \<Rightarrow> i" (infix "\<ominus>" 51)
  where "x \<ominus> y \<equiv> THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq> x \<and> D w y"

definition complement:: "i \<Rightarrow> i" ("\<midarrow>")
  where "\<midarrow> x \<equiv> THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x"

definition fusion:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<sigma>")
  where "\<sigma> F \<equiv> THE x. \<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O z y)"

abbreviation fusion_infix:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<sigma>" [8] 9)
  where "\<sigma> x. F x \<equiv> \<sigma> F" --  "general sum or fusion of the Fs"

definition strong_fusion:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<rho>")
  where "\<rho> F \<equiv> THE x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. y \<preceq> x \<longrightarrow> (\<exists> z. F z \<and> O y z))"

abbreviation strong_fusion_infix:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<rho>" [8] 9)
  where "\<rho> x. F x \<equiv> \<rho> F" --  "strong general sum or fusion of the Fs"

definition general_product:: "(i \<Rightarrow> bool) \<Rightarrow> i" ("\<pi>")
  where "\<pi> F \<equiv> \<sigma> x. \<forall> y. F y \<longrightarrow> x \<preceq> y"

abbreviation general_product_infix:: "(i \<Rightarrow> bool) \<Rightarrow> i" (binder "\<pi>" [8] 9)
  where "\<pi> x. F x \<equiv> \<pi> F"

end

section {* Ground Mereology *}

locale ground_mereology = mereology +
 assumes P_reflexivity: "x \<preceq> x"
 assumes P_antisymmetry: "x \<preceq> y \<longrightarrow> y \<preceq> x \<longrightarrow> x = y"
 assumes P_transitivity: "x \<preceq> y \<longrightarrow> y \<preceq> z \<longrightarrow> x \<preceq> z"

begin

interpretation partial_order: partial_order "(|carrier = set i, eq = op =, le = op \<preceq>|)"
  using P_reflexivity P_antisymmetry P_transitivity by unfold_locales auto

lemma "x = y \<longleftrightarrow> x \<preceq> y \<and> y \<preceq> x"
  using P_antisymmetry P_reflexivity by auto

lemma "x = y \<longleftrightarrow> (\<forall> z. z \<preceq> x \<longleftrightarrow> z \<preceq> y)"
  using P_antisymmetry P_reflexivity by blast

lemma "x = y \<longleftrightarrow> (\<forall> z. x \<preceq> z \<longleftrightarrow> y \<preceq> z)"
  using P_antisymmetry P_reflexivity by blast

lemma PP_asymmetry: "x \<prec> y \<longrightarrow> \<not> y \<prec> x"
  by (simp add: PP_def P_antisymmetry)

lemma PP_transitivity: "x \<prec> y \<longrightarrow> y \<prec> z \<longrightarrow> x \<prec> z"
  by (metis PP_def PP_asymmetry P_transitivity)

lemma "x \<prec> y \<longleftrightarrow> x \<preceq> y \<and> \<not> y \<preceq> x"
  using PP_def P_antisymmetry by auto

lemma "x \<preceq> y \<and> y \<prec> z \<longrightarrow> x \<prec> z"
  using PP_def PP_transitivity by blast

lemma "x \<prec> y \<and> y \<preceq> z \<longrightarrow> x \<prec> z"
  using PP_def PP_transitivity by blast

lemma O_reflexivity: "O x x"
  using O_def P_reflexivity by blast

lemma P_implies_O: "x \<preceq> y \<longrightarrow> O x y"
  using O_def P_reflexivity by auto

lemma "x \<preceq> y \<and> O x z \<longrightarrow> O y z"
  using O_def P_transitivity by blast

text {* The following lemma is important in @{cite "hovda_what_2009"} p. 66: *}

lemma overlap_lemma: "(\<exists> x. x \<preceq> y \<and> O x z) \<longrightarrow> O y z"
  using O_def P_transitivity by blast

lemma "(\<forall> z. z \<preceq> x \<longrightarrow> O z y) \<longleftrightarrow> (\<forall> z. O z x \<longrightarrow> O z y)"
  by (meson O_def P_transitivity P_implies_O)

lemma D_irreflexive: "\<not> D x x"
  by (simp add: D_def O_reflexivity)

lemma "x \<preceq> y \<and> D y z \<longrightarrow> D x z"
  by (meson D_def O_def P_transitivity)

lemma "U x x"
  using U_def P_reflexivity by blast

lemma  P_implies_U: "x \<preceq> y \<longrightarrow> U x y"
  using U_def P_reflexivity by auto

lemma "x \<preceq> y \<and> U y z \<longrightarrow> U x z"
  using U_def P_transitivity by blast

lemma "(\<forall> z. x \<preceq> z \<longrightarrow> U z y) \<longleftrightarrow> (\<forall> z. U z x \<longrightarrow> U z y)"
  by (metis U_def P_transitivity P_implies_U)

lemma product_idempotence: "x \<otimes> x = x"
proof -
  have "x \<otimes> x = (THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> x)"
    using product_def by simp
  also have  "(THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> x) = x"
  proof (rule the_equality)
    show "\<forall> w. w \<preceq> x \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> x)" by simp
    show "\<And> z. \<forall>w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> x) \<Longrightarrow> z = x"
      using P_antisymmetry P_reflexivity by blast
  qed
  finally show ?thesis
    by simp
qed

lemma product_intro: "(\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)) \<longrightarrow> x \<otimes> y = z"
proof
  assume antecedent: "\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"
  hence "(THE v. \<forall> w. w \<preceq> v \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> y) = z"
  proof (rule the_equality)
    show "\<And> v. \<forall> w. w \<preceq> v \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y) \<Longrightarrow> v = z "
      by (meson antecedent P_antisymmetry P_reflexivity)
  qed
  thus "x \<otimes> y = z"
    using product_def by auto
qed

lemma difference_intro: "(\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y)) \<longrightarrow> x \<ominus> y = z"
proof
  assume antecedent: "\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y)"
  hence "(THE v. \<forall> w. w \<preceq> v \<longleftrightarrow> (w \<preceq> x \<and> D w y)) = z"
  proof (rule the_equality)
    show "\<And>v. \<forall>w. (w \<preceq> v) = (w \<preceq> x \<and> D w y) \<Longrightarrow> v = z"
      by (meson antecedent P_antisymmetry P_reflexivity)
  qed
  thus "x \<ominus> y = z"
    by (simp add: difference_def)
qed

lemma no_diff: "D x y \<longrightarrow> x \<ominus> y = x"
proof
  assume "D x y"
  hence "\<forall> w. w \<preceq> x \<longleftrightarrow> (w \<preceq> x \<and> D w y)"
    by (meson D_def O_def P_transitivity)
  with difference_intro show "x \<ominus> y = x"..
qed

lemma complement_intro: "(\<forall> w. w \<preceq> y \<longleftrightarrow> D w x) \<longrightarrow> (\<midarrow> x) = y"
proof
  assume antecedent: "\<forall> w. w \<preceq> y \<longleftrightarrow> D w x"
  hence "(THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x) = y"
  proof (rule the_equality)
    show "\<And>z. \<forall>w. (w \<preceq> z) = D w x \<Longrightarrow> z = y"
      using antecedent P_antisymmetry P_reflexivity by blast
  qed
  thus "(\<midarrow> x) = y"
    using complement_def by auto
qed

end

section {* Minimal Mereology *}

locale minimal_mereology = ground_mereology +
  assumes weak_supplementation: "x \<prec> y \<longrightarrow> (\<exists> z. z \<preceq> y \<and> D z x)"

begin

lemma proper_weak_supplementation: "(\<forall> x. \<forall> y. x \<prec> y \<longrightarrow> (\<exists> z. z \<prec> y \<and> D z x))"
  by (metis D_def D_symmetry P_implies_O
PP_def weak_supplementation)

lemma company: "x \<prec> y \<longrightarrow> (\<exists> z. z \<noteq> x \<and> z \<prec> y)"
  using D_irreflexive proper_weak_supplementation by force

lemma strong_company: "x \<prec> y \<longrightarrow> (\<exists> z. z \<prec> y \<and> \<not> z \<preceq> x)"
  by (meson D_def P_implies_O proper_weak_supplementation)

end

section {* Extensional Mereology *}

locale extensional_mereology = ground_mereology +
  assumes strong_supplementation: "\<not> x \<preceq> y \<longrightarrow> (\<exists> z. z \<preceq> x \<and> D z y)"

begin

lemma proper_parts_principle:  "(\<exists> z. z \<prec> x) \<longrightarrow> (\<forall> z. z \<prec> x \<longrightarrow> z \<preceq> y) \<longrightarrow> x \<preceq> y"
  by (metis D_def O_def PP_def P_reflexivity strong_supplementation)

lemma extensionality: "(\<exists> z. z \<prec> x \<or> z \<prec> y) \<longrightarrow> (\<forall> z. z \<prec> x \<longleftrightarrow> z \<prec> y) \<longrightarrow> x = y"
  by (meson PP_def P_antisymmetry proper_parts_principle)

lemma weak_supplementation: "x \<prec> y \<longrightarrow> (\<exists> z. z \<preceq> y \<and> D z x)"
  using PP_def P_antisymmetry strong_supplementation by blast

lemma P_iff_all_P_O: "x \<preceq> y \<longleftrightarrow> (\<forall> z. z \<preceq> x \<longrightarrow> O z y)"
  using D_def P_transitivity P_implies_O strong_supplementation by blast

lemma P_iff_all_O_O: "x \<preceq> y \<longleftrightarrow> (\<forall> z. O z x \<longrightarrow> O z y)"
  by (meson O_def P_transitivity P_iff_all_P_O)

lemma O_extensionality: "x = y \<longleftrightarrow> (\<forall> z. O x z \<longleftrightarrow> O y z)"
  by (meson D_def O_symmetry P_antisymmetry P_implies_O strong_supplementation)

lemma P_iff_all_D_D: "x \<preceq> y \<longleftrightarrow> (\<forall> z. D z y \<longrightarrow> D z x)"
  by (metis D_def P_transitivity O_def strong_supplementation)

lemma "x \<preceq> y \<longleftrightarrow> (\<forall> z. D z y \<longrightarrow> \<not> z \<preceq> x)"
  by (meson D_def P_transitivity P_implies_O strong_supplementation)

lemma D_extensionality: "x = y \<longleftrightarrow> (\<forall> z. D z x \<longleftrightarrow> D z y)"
  by (metis D_def PP_def P_implies_O strong_supplementation weak_supplementation)

lemma sum_idempotence: "x \<oplus> x = x"
proof -
  have "x \<oplus> x = (THE z. \<forall> w. O w z \<longleftrightarrow> O w x \<or> O w x)"
    using sum_def by simp
  also have "\<dots> = x"
  proof (rule the_equality)
    show "\<forall> w. O w x \<longleftrightarrow> (O w x \<or> O w x)" by simp
    show "\<And>z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w x) \<Longrightarrow> z = x"
      by (meson D_def D_extensionality)
  qed
  finally show "x \<oplus> x = x" by simp
qed

lemma sum_intro:
   "(\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) \<longrightarrow> y \<oplus> z = x"
proof
  assume antecedent: "\<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)"
  hence "(THE x. \<forall> w. O w x \<longleftrightarrow> (O w y \<or> O w z)) = x"
  proof (rule the_equality)
    show "\<And> a. \<forall>w. O w a \<longleftrightarrow> (O w y \<or> O w z) \<Longrightarrow> a = x"
      by (meson antecedent O_extensionality O_symmetry)
  qed
  thus "y \<oplus> z = x"
    using sum_def by blast
qed

lemma u_intro: "(\<forall> y. y \<preceq> x) \<longrightarrow> x = u"
  by (simp add: P_antisymmetry the_equality u_def)

lemma fusion_absorption: "(\<sigma> z. z \<preceq> x) = x"
proof -
  have "(THE v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. z \<preceq> x \<and> O z y)) = x"
  proof (rule the_equality)
    show "\<forall> y. O y x \<longleftrightarrow> (\<exists>z. z \<preceq> x \<and> O z y)"
      using O_symmetry P_iff_all_O_O by blast
    thus "\<And> v. \<forall> y. O y v \<longleftrightarrow> (\<exists> z. z \<preceq> x \<and> O z y) \<Longrightarrow> v = x"
      by (metis sum_intro)
  qed
  thus "(\<sigma> z. z \<preceq> x) = x"
    by (simp add: fusion_def)
qed

lemma fusion_intro: "(\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) \<longrightarrow> (\<sigma> x. F x) = z"
proof
  assume antecedent: "(\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
  hence "(THE v. \<forall> y. O y v \<longleftrightarrow> (\<exists> x. F x \<and> O x y)) = z"
  proof (rule the_equality)
    show "\<And> v. \<forall> y. O y v \<longleftrightarrow> (\<exists>x. F x \<and> O x y) \<Longrightarrow> v = z"
      by (metis antecedent sum_intro)
  qed
  thus "(\<sigma> v. F v) = z"
    using fusion_def by blast
qed

lemma fusion_idempotence: "(\<sigma> z. z = x) = x"
  by (metis (full_types) fusion_intro O_symmetry)

lemma general_product_idempotence: "x = (\<pi> z. z = x)"
proof -
  have "(\<pi> z. z = x) = (\<sigma> z. \<forall> y. x = y \<longrightarrow> z \<preceq> y)"
    by (simp add: general_product_def)
  also have "... = (THE z. \<forall> y. O y z \<longleftrightarrow> (\<exists> v. (\<forall> j. x = j \<longrightarrow> v \<preceq> j) \<and> O v y))"
    using fusion_def by simp
  also have "... = x"
  proof (rule the_equality)
    show "\<forall>y. O y x = (\<exists>v. (\<forall> j. x = j \<longrightarrow> v \<preceq> j) \<and> O v y)"
      using O_symmetry P_iff_all_O_O by blast
    thus "\<And>z. \<forall> y. O y z = (\<exists>v. (\<forall> j. x = j \<longrightarrow> v \<preceq> j) \<and> O v y) \<Longrightarrow> z = x"
      by (metis sum_intro)
  qed
  finally show "x = (\<pi> z. z = x)" by simp
qed

lemma general_product_absorption: "x = (\<pi> z. x \<preceq> z)"
proof -
  have "(\<pi> z. x \<preceq> z) = (\<sigma> z. \<forall> y. x \<preceq> y \<longrightarrow> z \<preceq> y)"
    by (simp add: general_product_def)
  also have "... = (THE z. \<forall> y. O y z \<longleftrightarrow> (\<exists> v. (\<forall> j. x \<preceq> j \<longrightarrow> v \<preceq> j)  \<and> O v y))"
    using fusion_def by simp
  also have "... = x"
  proof (rule the_equality)
    show "\<forall>y. O y x = (\<exists>v. (\<forall>j. x \<preceq> j \<longrightarrow> v \<preceq> j) \<and> O v y)"
      by (meson O_def P_reflexivity P_transitivity)
    thus "\<And>z. \<forall>y. O y z = (\<exists>v. (\<forall>j. x \<preceq> j \<longrightarrow> v \<preceq> j) \<and> O v y) \<Longrightarrow> z = x"
      by (metis P_antisymmetry P_implies_O P_iff_all_P_O)
  qed
  finally show "x = (\<pi> z. x \<preceq> z)"
    by simp
qed

lemma strong_fusion_intro:
"((\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. y \<preceq> x \<longrightarrow> (\<exists> z. F z \<and> O y z))) \<longrightarrow> (\<rho> v. F v) = x"
proof
  assume antecedent: "((\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. y \<preceq> x \<longrightarrow> (\<exists> z. F z \<and> O y z)))"
  hence "(THE x. (\<forall>y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall>y. y \<preceq> x \<longrightarrow> (\<exists>z. F z \<and> O y z))) = x"
  proof (rule the_equality)
    show "\<And>xa. (\<forall>y. F y \<longrightarrow> y \<preceq> xa) \<and> (\<forall>y. y \<preceq> xa \<longrightarrow> (\<exists>z. F z \<and> O y z)) \<Longrightarrow> xa = x"
    proof -
      fix xa
      show "(\<forall>y. F y \<longrightarrow> y \<preceq> xa) \<and> (\<forall>y. y \<preceq> xa \<longrightarrow> (\<exists>z. F z \<and> O y z)) \<Longrightarrow> xa = x"
      proof -
        assume "(\<forall>y. F y \<longrightarrow> y \<preceq> xa) \<and> (\<forall>y. y \<preceq> xa \<longrightarrow> (\<exists>z. F z \<and> O y z))"
        thus "xa = x"
          by (meson antecedent P_antisymmetry P_iff_all_O_O P_iff_all_P_O)
      qed
    qed
  qed
  thus "(\<rho> v. F v) = x"
    using strong_fusion_def by simp
qed

end

sublocale extensional_mereology \<subseteq> minimal_mereology
  by (simp add: ground_mereology_axioms minimal_mereology_axioms.intro minimal_mereology_def weak_supplementation)

subsection {* Closure Mereology *}

locale closure_mereology = ground_mereology +
  assumes sum_closure: "U x y \<longrightarrow> (\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))"
-- "sum closure"
  assumes product_closure: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"
-- "product closure"

begin

lemma product_character: "O x y \<longrightarrow> (\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"
proof
  assume "O x y"
  with product_closure have "\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"..
  then obtain z where z: "\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"..
  with product_intro have "x \<otimes> y = z"..
  thus "(\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"
    by (simp add: z)
qed

lemma in_first_factor: "O x y \<longrightarrow> x \<otimes> y \<preceq> x"
  using P_reflexivity product_character by blast

lemma in_second_factor: "O x y \<longrightarrow> x \<otimes> y \<preceq> y"
  using P_reflexivity product_character by blast

lemma "O x y \<and> z \<preceq> x \<otimes> y \<longrightarrow> z \<preceq> x"
  using product_character by blast

lemma "O x y \<and> z \<preceq> x \<otimes> y \<longrightarrow> z \<preceq> y"
  using product_character by blast

lemma product_absorption: "x \<preceq> y \<longrightarrow> x \<otimes> y = x"
  using P_antisymmetry P_reflexivity P_implies_O product_character by blast

lemma  "O x y \<and> x = x \<otimes> y \<longrightarrow> x \<preceq> y"
  using in_second_factor by force

lemma product_overlap: "O x y \<and> O w (x \<otimes> y) \<longrightarrow> O w x"
  using O_def product_character by blast

lemma "x \<noteq> y \<and> O x y \<longrightarrow> x \<otimes> y \<prec> x \<or> x \<otimes> y \<prec> y"
  by (simp add: in_first_factor in_second_factor PP_def)

lemma product_association: "(\<exists> w. w \<preceq> x \<and> w \<preceq> y \<and> w \<preceq> z) \<longrightarrow> x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z"
proof
  assume antecedent: "(\<exists> w. w \<preceq> x \<and> w \<preceq> y \<and> w \<preceq> z)"
  hence "O y z"
    using O_def by auto
  with product_character have yz: "\<forall> w. w \<preceq> (y \<otimes> z) \<longleftrightarrow> (w \<preceq> y \<and> w \<preceq> z)"..
  hence "O x (y \<otimes> z)"
    by (simp add: antecedent O_def)
  with product_character have "\<forall> w. w \<preceq> (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> (y \<otimes> z))"..
  hence xyz: "\<forall> w. w \<preceq> (x \<otimes> (y \<otimes> z)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y \<and> w \<preceq> z)"
    using yz by simp
  from antecedent have "O x y"
    using O_def by auto
  with product_character have xy: "(\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"..
  hence "O (x \<otimes> y) z"
    by (simp add: antecedent O_def)
  with product_character have "\<forall> w. w \<preceq> ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> (w \<preceq> (x \<otimes> y)) \<and> w \<preceq> z"..
  hence  "\<forall> w. w \<preceq> ((x \<otimes> y) \<otimes> z) \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> y \<and> w \<preceq> z"
    using xy by simp
  thus "x \<otimes> (y \<otimes> z) = (x \<otimes> y) \<otimes> z"
    using xyz P_antisymmetry P_reflexivity by blast
qed

end

section {* Closed Extensional Mereology *}

locale closed_minimal_mereology = closure_mereology + minimal_mereology

begin

lemma strong_supplementation: "\<not> x \<preceq> y \<longrightarrow> (\<exists> z. z \<preceq> x \<and> D z y)"
proof fix x y
  assume "\<not> x \<preceq> y"
  show "(\<exists> z. z \<preceq> x \<and> D z y)"
  proof cases
    assume "D x y"
    thus "(\<exists> z. z \<preceq> x \<and> D z y)"
      using P_reflexivity by auto
  next
    assume "\<not> D x y"
    hence "O x y"
      using D_def by simp
    with product_character have product: "\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"..
    hence "x \<otimes> y \<prec> x"
      using \<open>\<not> x \<preceq> y\<close> P_reflexivity PP_def by auto
    with weak_supplementation have "\<exists> z. z \<preceq> x \<and> D z (x \<otimes> y)"..
    then obtain c where c: "c \<preceq> x \<and> D c (x \<otimes> y)"..
    hence "c \<preceq> x \<and> D c y"
      by (meson D_def O_def P_transitivity product)
    thus "\<exists> z. z \<preceq> x \<and> D z y"..
  qed
qed

end

locale closed_extensional_mereology = extensional_mereology + closure_mereology

sublocale closed_extensional_mereology \<subseteq> closed_minimal_mereology
  by (simp add: closed_minimal_mereology_def closure_mereology_axioms minimal_mereology_axioms)

sublocale closed_minimal_mereology \<subseteq> closed_extensional_mereology
proof
  show "\<And>x y. \<not> x \<preceq> y \<longrightarrow> (\<exists>z. z \<preceq> x \<and> D z y)"
    using strong_supplementation by simp
qed

context closed_extensional_mereology
begin

lemma underlap_implies_sum_character: "U x y \<longrightarrow> (\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y))"
proof
  assume "U x y"
  with sum_closure have "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))"..
  then obtain a where a: "\<forall> w. O w a \<longleftrightarrow> (O w x \<or> O w y)"..
  with sum_intro have "x \<oplus> y = a"..
  thus "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)" using a by simp
qed

lemma conditonal_sum_associativity: 
"(\<exists> v. x \<preceq> v \<and> y \<preceq> v \<and> z \<preceq> v) \<longrightarrow>  x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
proof
  assume antecedent: "\<exists> v. x \<preceq> v \<and> y \<preceq> v \<and> z \<preceq> v"
  hence "U x y"
    using U_def by auto
  with underlap_implies_sum_character have xy: "(\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y))"..
   hence "U (x \<oplus> y) z"
    using U_def antecedent P_iff_all_O_O by auto
  with underlap_implies_sum_character have "(\<forall> w. O w ((x \<oplus> y) \<oplus> z) \<longleftrightarrow> (O w (x \<oplus> y) \<or> O w z))"..
  hence xyz: "\<forall> w. O w ((x \<oplus> y) \<oplus> z) \<longleftrightarrow> (O w x \<or> O w y \<or> O w z)"
    using xy by simp  
  have "U y z"
    using antecedent U_def by auto
  with underlap_implies_sum_character have yz: "(\<forall> w. O w (y \<oplus> z) \<longleftrightarrow> (O w y \<or> O w z))"..
  hence "U x (y \<oplus> z)"
    using U_def antecedent P_iff_all_O_O by auto
  with underlap_implies_sum_character have "(\<forall> w. O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> (O w x \<or> O w (y \<oplus> z)))"..
  hence "\<forall> w. O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow> (O w x \<or> O w y \<or> O w z)"
    using yz by simp
  hence "\<forall> w. O w (x \<oplus> (y \<oplus> z)) \<longleftrightarrow>  O w ((x \<oplus> y) \<oplus> z)"
    using xyz by simp
  thus "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
    using P_iff_all_O_O P_antisymmetry by auto
qed

lemma sums_of_parts: "x \<preceq> z \<and> y \<preceq> z \<longrightarrow> x \<oplus> y \<preceq> z"
proof
  assume "x \<preceq> z \<and> y \<preceq> z"
  hence "U x y"
    using U_def by blast
  with underlap_implies_sum_character have "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)"..
  thus "x \<oplus> y \<preceq> z"
    using P_iff_all_O_O \<open>x \<preceq> z \<and> y \<preceq> z\<close> by auto
qed

lemma part_summand_absorption: "y \<preceq> x \<longrightarrow> x = x \<oplus> y"
  by (metis sum_intro P_iff_all_O_O)

end

section {* Closed Extensional Mereology with Universe *}

locale closure_mereology_with_universe = closure_mereology +
  assumes universe_closure: "\<exists> z. \<forall> x. x \<preceq> z"

begin

lemma universal_underlap: "U x y"
  by (metis U_def universe_closure)

lemma unconditional_sum_closure: "(\<exists> z. \<forall> w. O w z \<longleftrightarrow> (O w x \<or> O w y))"
  by (simp add: sum_closure universal_underlap)

lemma u_intro: "(\<forall> x. x \<preceq> z) \<longrightarrow> u = z"
proof
  assume "\<forall> x. x \<preceq> z"
  hence "(THE y. \<forall> x. x \<preceq> y) = z"
  proof (rule the_equality)
    show "\<And> y. \<forall> x. x \<preceq> y \<Longrightarrow> y = z"
      by (simp add: \<open>\<forall>x. x \<preceq> z\<close> P_antisymmetry)
  qed
  thus "u = z"
    by (simp add: u_def)
qed

lemma u_character: "\<forall> x. x \<preceq> u"
  using universe_closure u_intro by blast

lemma "u \<preceq> x \<longrightarrow> u = x"
  by (simp add: P_antisymmetry u_character)

lemma "\<not> u \<prec> x"
  by (simp add: P_antisymmetry PP_def u_character)

lemma multiplicative_identity: "x \<otimes> u = x"
  by (simp add: product_intro u_character)

end

locale closed_extensional_mereology_with_universe = closure_mereology_with_universe +
  closed_extensional_mereology

begin

lemma annulment: "x \<oplus> u = u"
  using part_summand_absorption sum_commutative u_character by auto

lemma sum_character: "\<forall> w. O w (x \<oplus> y) \<longleftrightarrow> (O w x \<or> O w y)"
  by (simp add: underlap_implies_sum_character universal_underlap)

lemma sum_associativity: "x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
  using conditonal_sum_associativity u_character by blast

lemma first_summand_inclusion: "x \<preceq> x \<oplus> y"
  by (simp add: P_iff_all_O_O sum_character)

lemma second_summand_inclusion: "y \<preceq> x \<oplus> y"
  using first_summand_inclusion sum_commutative by fastforce

lemma summand_inclusion: "x \<oplus> y \<preceq> z \<longleftrightarrow> x \<preceq> z \<and> y \<preceq> z"
  using first_summand_inclusion P_transitivity second_summand_inclusion
sums_of_parts by blast

lemma disjoint_proper_summands: "D x y \<longrightarrow> x \<prec> x \<oplus> y \<and> y \<prec> x \<oplus> y"
  by (metis D_def D_symmetry first_summand_inclusion P_implies_O
PP_def second_summand_inclusion)

lemma proper_summand: "\<not> x \<preceq> y \<longrightarrow> y \<prec> x \<oplus> y"
  by (metis first_summand_inclusion PP_def second_summand_inclusion)

lemma distinct_iff_proper_summands: "x \<noteq> y \<longleftrightarrow> x \<prec> x \<oplus> y \<or> y \<prec> x \<oplus> y"
  using first_summand_inclusion PP_def second_summand_inclusion sum_idempotence by auto

lemma absorption_iff_P: "x = x \<oplus> y \<longleftrightarrow> y \<preceq> x"
  by (metis part_summand_absorption second_summand_inclusion)

lemma summand_part: "(x \<preceq> y \<oplus> z \<and> D x z) \<longrightarrow> x \<preceq> y"
proof
  assume antecedent: "x \<preceq> y \<oplus> z \<and> D x z"
  have "\<forall> w. O w (y \<oplus> z) \<longleftrightarrow> (O w y \<or> O w z)" using sum_character.
  thus "x \<preceq> y"
    by (meson antecedent D_def O_symmetry P_iff_all_O_O P_iff_all_P_O)
qed

lemma proper_sum_monotonicity: "x \<prec> y \<and> D y z \<longrightarrow> x \<oplus> z \<prec> y \<oplus> z"
  by (metis absorption_iff_P summand_part PP_def sum_commutative 
second_summand_inclusion summand_inclusion)

text {* The following proof is adapted from @{cite "pietrusczczak_metamereology_2018"}, p. 96: *}

lemma disjoint_sum_parts: "v \<preceq> x \<oplus> y \<and> v \<preceq> x \<oplus> z \<and> D y z \<longrightarrow> v \<preceq> x" 
proof
  assume antecedent: "v \<preceq> x \<oplus> y \<and> v \<preceq> x \<oplus> z \<and> D y z"
  show "v \<preceq> x"
  proof (rule ccontr)
    assume "\<not> v \<preceq> x"
    with strong_supplementation have "(\<exists> w. w \<preceq> v \<and> D w x)"..
    then obtain w where "w \<preceq> v \<and> D w x"..
    hence "w \<preceq> x \<oplus> y \<and> w \<preceq> x \<oplus> z"
      using P_transitivity antecedent by blast
    hence "w \<preceq> y \<and> w \<preceq> z"
      by (metis \<open>w \<preceq> v \<and> D w x\<close> sum_commutative summand_part)
    hence "\<not> D y z"
      using O_def D_def by blast
    thus "False"
      using antecedent by blast
  qed
qed

text {* The following proofs concerning distributivity are from @{cite "pietrusczczak_metamereology_2018"}, pp. 103-4: *}

lemma disjoint_implies_product_of_sums: "D y z \<longrightarrow> (x \<oplus> y) \<otimes> (x \<oplus> z) = x"
proof
  assume antecedent: "D y z"
  have left_to_right: "x \<preceq> (x \<oplus> y) \<otimes> (x \<oplus> z)"
    using O_def first_summand_inclusion product_character by blast
  have "\<forall> v. v \<preceq> (x \<oplus> y) \<otimes> (x \<oplus> z) \<longrightarrow> v \<preceq> x"
  proof
    fix v
    show "v \<preceq> (x \<oplus> y) \<otimes> (x \<oplus> z) \<longrightarrow> v \<preceq> x"
    proof
      assume "v \<preceq> (x \<oplus> y) \<otimes> (x \<oplus> z)"
      hence "v \<preceq> x \<oplus> y \<and> v \<preceq> x \<oplus> z"
        using O_def first_summand_inclusion product_character by blast
      hence "(v \<preceq> x \<oplus> y \<and> v \<preceq> x \<oplus> z) \<and> D y z" using antecedent..
      thus "v \<preceq> x"
        using disjoint_sum_parts by blast
    qed
  qed
  hence right_to_left: "(x \<oplus> y) \<otimes> (x \<oplus> z) \<preceq> x"
    using P_reflexivity by blast
  thus "(x \<oplus> y) \<otimes> (x \<oplus> z) = x"
    using P_antisymmetry left_to_right by blast
qed

lemma product_parts: "O x y \<and> x \<preceq> z \<and> y \<preceq> v \<longrightarrow> x \<otimes> y \<preceq> z \<otimes> v"
proof
  assume antecedent: "O x y \<and> x \<preceq> z \<and> y \<preceq> v"
  hence "O z v"
    using O_symmetry P_iff_all_O_O by blast
  hence "\<forall> w. w \<preceq> x \<otimes> y \<longrightarrow> w \<preceq> z \<otimes> v"
    using P_transitivity antecedent product_character by auto
  thus "x \<otimes> y \<preceq> z \<otimes> v"
    using P_reflexivity by auto
qed

lemma sum_product_distribution: "O y z \<longrightarrow> x \<oplus> (y \<otimes> z) = (x \<oplus> y) \<otimes> (x \<oplus> z)"
proof
  assume antecedent: "O y z"
  have "y \<preceq> x \<oplus> y \<and> z \<preceq> x \<oplus> z"
    by (simp add: second_summand_inclusion)
  hence "y \<otimes> z \<preceq> (x \<oplus> y) \<otimes> (x \<oplus> z)"
    using antecedent product_parts by simp
  hence left_to_right: "x \<oplus> (y \<otimes> z) \<preceq> (x \<oplus> y) \<otimes> (x \<oplus> z)"
    by (metis first_summand_inclusion O_def product_character sums_of_parts)
  have right_to_left: "(x \<oplus> y) \<otimes> (x \<oplus> z) \<preceq> x \<oplus> (y \<otimes> z)"
  proof (rule ccontr)
    assume "\<not> (x \<oplus> y) \<otimes> (x \<oplus> z) \<preceq> x \<oplus> (y \<otimes> z)"
    with strong_supplementation have "(\<exists> v. v \<preceq> ((x \<oplus> y) \<otimes> (x \<oplus> z)) \<and> D v (x \<oplus> (y \<otimes> z)))"..
    then obtain v where v: "v \<preceq> ((x \<oplus> y) \<otimes> (x \<oplus> z)) \<and> D v (x \<oplus> (y \<otimes> z))"..
    hence "v \<preceq> ((x \<oplus> y) \<otimes> (x \<oplus> z))"..
    hence "v \<preceq> x \<oplus> y \<and> v \<preceq> x \<oplus> z"
      using O_def first_summand_inclusion product_character by blast
    from v have "D v (x \<oplus> (y \<otimes> z))"..
    hence "D v x \<and> D v (y \<otimes> z)"
      by (simp add: D_def sum_character)
    hence "v \<preceq> y \<and> v \<preceq>  z"
      by (metis \<open>v \<preceq> x \<oplus> y \<and> v \<preceq> x \<oplus> z\<close> sum_commutative summand_part)
    hence "v \<preceq> y \<otimes> z"
      using O_def product_character by blast
    thus "False"
      using D_def P_implies_O \<open>D v x \<and> D v (y \<otimes> z)\<close> by blast
  qed
  thus "x \<oplus> (y \<otimes> z) = (x \<oplus> y) \<otimes> (x \<oplus> z)"
    using P_antisymmetry left_to_right by blast
qed

lemma product_absorbs_disjoint_second_sum: "O x y \<and> D x z \<longrightarrow> x \<otimes> (y \<oplus> z) = x \<otimes> y"
proof
  assume antecedent: "O x y \<and> D x z"
  hence "x \<otimes> y \<preceq> x \<and> x \<otimes> y \<preceq> y \<and> y \<preceq> y \<oplus> z"
    by (simp add: first_summand_inclusion in_first_factor in_second_factor)
  hence right_to_left: "x \<otimes> y \<preceq> x \<otimes> (y \<oplus> z)"
    by (simp add: P_reflexivity antecedent product_parts)
  have left_to_right: "x \<otimes> (y \<oplus> z) \<preceq> x \<otimes> y"
  proof (rule ccontr)
    assume "\<not> x \<otimes> (y \<oplus> z) \<preceq> x \<otimes> y"
    with strong_supplementation have "\<exists> v. v \<preceq> (x \<otimes> (y \<oplus> z)) \<and> D v (x \<otimes> y)"..
    then obtain v where v: "v \<preceq> (x \<otimes> (y \<oplus> z)) \<and> D v (x \<otimes> y)"..
    hence "v \<preceq> x \<and> v \<preceq> y \<oplus> z"
      using antecedent product_character sum_character by blast
    hence "D v y"
      by (metis D_symmetry P_iff_all_D_D P_implies_O antecedent product_character D_def summand_part v)
    hence "D v z"
      using P_iff_all_D_D \<open>v \<preceq> x \<and> v \<preceq> y \<oplus> z\<close> antecedent D_symmetry by blast
    hence "O x z"
      using P_implies_O \<open>D v y\<close> \<open>v \<preceq> x \<and> v \<preceq> y \<oplus> z\<close> D_def summand_part by blast
    thus "False"
      using D_def antecedent by blast
  qed
  thus "x \<otimes> (y \<oplus> z) = x \<otimes> y"
 using P_antisymmetry right_to_left by blast
qed

lemma product_absorbs_disjoint_first_sum: "D x y \<and> O x z \<longrightarrow> x \<otimes> (y \<oplus> z) = x \<otimes> z"
  using sum_commutative product_absorbs_disjoint_second_sum by force

lemma product_overlap: "z \<preceq> x \<and> O z y \<longrightarrow> O x y \<and> O z (x \<otimes> y)"
proof
  assume "z \<preceq> x \<and> O z y"
  hence "\<exists> v. v \<preceq> z \<and> v \<preceq> y"
    by (simp add: O_def)
  then obtain v where v: "v \<preceq> z \<and> v \<preceq> y"..
  hence "v \<preceq> x \<and> v \<preceq> y"
    using P_transitivity \<open>z \<preceq> x \<and> O z y\<close> by blast
  hence "O x y"
    using O_def by blast
  thus "O x y \<and> O z (x \<otimes> y)"
    using O_def \<open>v \<preceq> x \<and> v \<preceq> y\<close> product_character v by blast
qed


lemma product_sum_distribution: "O x y \<and> O x z \<longrightarrow> x \<otimes> (y \<oplus> z) = (x \<otimes> y) \<oplus> (x \<otimes> z)"
proof
  assume "O x y \<and> O x z"
  hence right_to_left: "(x \<otimes> y) \<oplus> (x \<otimes> z) \<preceq> x \<otimes> (y \<oplus> z)"
    by (meson P_reflexivity product_parts summand_inclusion)
  have left_to_right: "x \<otimes> (y \<oplus> z) \<preceq> (x \<otimes> y) \<oplus> (x \<otimes> z)"
  proof (rule ccontr)
    assume "\<not> x \<otimes> (y \<oplus> z) \<preceq> (x \<otimes> y) \<oplus> (x \<otimes> z)"
    with strong_supplementation have "\<exists> v. v \<preceq> (x \<otimes> (y \<oplus> z)) \<and> D v ((x \<otimes> y) \<oplus> (x \<otimes> z))"..
    then obtain v where v: "v \<preceq> (x \<otimes> (y \<oplus> z)) \<and> D v ((x \<otimes> y) \<oplus> (x \<otimes> z))"..
    hence "v \<preceq> x \<and> v \<preceq> y \<oplus> x \<and> D v (x \<otimes> y) \<and> D v (x \<otimes> z)"
      by (meson P_iff_all_D_D \<open>O x y \<and> O x z\<close> first_summand_inclusion product_character second_summand_inclusion sum_character)
    hence "D v y \<and> D v z"
      using D_def product_overlap by blast
    hence "D v (y \<oplus> z)"
      by (simp add: D_def sum_character)
    thus "False"
      by (meson P_implies_O \<open>O x y \<and> O x z\<close> sum_character D_def product_character v)
  qed
  thus "x \<otimes> (y \<oplus> z) = (x \<otimes> y) \<oplus> (x \<otimes> z)"
 using P_antisymmetry right_to_left by blast
qed

lemma part_of_sum_is_sum_of_products: "O x y \<and> O x z \<and> x \<preceq> (y \<oplus> z) \<longrightarrow> ((x \<otimes> y) \<oplus> (x \<otimes> z)) = x"
proof
  assume antecedent: "O x y \<and> O x z \<and> x \<preceq> (y \<oplus> z)"
  hence "O x y \<and> O x z"
    by simp
  hence "x \<otimes> (y \<oplus> z) = (x \<otimes> y) \<oplus> (x \<otimes> z)"
    using product_sum_distribution by simp
  also have "x \<otimes> (y \<oplus> z) = x"
    by (simp add: antecedent product_absorption) 
  thus "((x \<otimes> y) \<oplus> (x \<otimes> z)) = x"
    using calculation by auto
qed

lemma disjoint_summand_identity: "D x w \<and> D y v \<longrightarrow> x \<oplus> y = w \<oplus> v \<longrightarrow>  x = v \<and> y = w"
  by (metis P_antisymmetry D_symmetry sum_commutative second_summand_inclusion summand_part)

end

section {* Closed Extensional Mereology with Differences *}

locale closure_mereology_with_differences = closure_mereology +
  assumes difference_closure: "(\<exists> w. w \<preceq> x \<and> D w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y))"

begin

lemma difference_character:  "(\<exists> w. w \<preceq> x \<and> D w y) \<longrightarrow> (\<forall> w. w \<preceq> (x \<ominus> y) \<longleftrightarrow> (w \<preceq> x \<and> D w y))"
proof
  assume "(\<exists> w. w \<preceq> x \<and> D w y)"
  with difference_closure have "(\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y))"..
  then obtain z where z: "\<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y)"..
  with difference_intro have "(x \<ominus> y) = z"..
  thus "\<forall> w. w \<preceq> (x \<ominus> y) \<longleftrightarrow> (w \<preceq> x \<and> D w y)"
    using z by simp
qed

end

locale closed_extensional_mereology_with_differences =
closed_extensional_mereology + closure_mereology_with_differences

begin

lemma proper_difference: "(O x y \<and> \<not> x \<preceq> y) \<longrightarrow> (x \<ominus> y) \<prec> x"
proof
  assume "O x y \<and> \<not> x \<preceq> y"
  hence "\<not> x \<preceq> y"..
  with strong_supplementation have "(\<exists> w. w \<preceq> x \<and> D w y)"..
  with difference_character have "\<forall> w. w \<preceq> (x \<ominus> y) \<longleftrightarrow> (w \<preceq> x \<and> D w y)"..
  thus "(x \<ominus> y) \<prec> x"
    using \<open>O x y \<and> \<not> x \<preceq> y\<close> D_def P_reflexivity PP_def by auto
qed

lemma proper_proper_difference: "x \<prec> y \<longrightarrow> y \<ominus> x \<prec> y"
  using O_symmetry P_implies_O proper_difference PP_asymmetry
PP_def by blast

lemma no_diff_implies_disjoint: "\<not> y \<preceq> x \<and> y \<ominus> x = y \<longrightarrow> D x y"
  using D_def D_symmetry proper_difference PP_def by blast

lemma proper_difference_absorption: "x \<prec> y \<longrightarrow> x \<oplus> (y \<ominus> x) = y"
proof
  assume "x \<prec> y"
  with weak_supplementation have "(\<exists> w. w \<preceq> y \<and> D w x)"..
  with difference_character have difference: "\<forall> w. w \<preceq> (y \<ominus> x) \<longleftrightarrow> (w \<preceq> y \<and> D w x)"..
  hence "U x (y \<ominus> x)"
    by (metis \<open>x \<prec> y\<close> PP_def U_def P_reflexivity)
  with underlap_implies_sum_character have "\<forall> w. O w (x \<oplus> (y \<ominus> x)) \<longleftrightarrow> O w x \<or> O w (y \<ominus> x)"..
  hence "\<forall> w. O w (x \<oplus> (y \<ominus> x)) \<longleftrightarrow> O w y \<or> (O w y \<and> D w x)"
    by (metis \<open>x \<prec> y\<close> difference D_def P_iff_all_O_O O_def O_symmetry PP_def)
  hence  "\<forall> w. O w (x \<oplus> (y \<ominus> x)) \<longleftrightarrow> O w y"
    by blast
  thus "x \<oplus> (y \<ominus> x) = y"
    by (simp add: P_antisymmetry P_iff_all_O_O)
qed
  
lemma difference_absorbs_product: "O x y \<and> \<not> x \<preceq> y \<longrightarrow> x \<ominus> (x \<otimes> y) = x \<ominus> y"
proof
  assume "O x y \<and> \<not> x \<preceq> y"
  hence "\<not> x \<preceq> y"..
  with strong_supplementation have "\<exists> w. w \<preceq> x \<and> D w y"..
  with difference_character have right: "\<forall> w. w \<preceq> (x \<ominus> y) \<longleftrightarrow> (w \<preceq> x \<and> D w y)"..
  have "O x y" using \<open>O x y \<and> \<not> x \<preceq> y\<close>..
  with product_character have product: "\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"..
  hence "\<not> x \<preceq> (x \<otimes> y)"
    using \<open>O x y \<and> \<not> x \<preceq> y\<close> by blast
  with strong_supplementation have "\<exists> w. w \<preceq> x \<and> D w (x \<otimes> y)"..
  with difference_character have left: "\<forall> w. w \<preceq> (x \<ominus> (x \<otimes> y)) \<longleftrightarrow> (w \<preceq> x \<and> D w (x \<otimes> y))".. 
  hence "\<forall> w. w \<preceq> (x \<ominus> (x \<otimes> y)) \<longleftrightarrow> (w \<preceq> x \<and> D w (x \<otimes> y))"
    by (simp add: D_def)
  hence "\<forall> w. w \<preceq> (x \<ominus> (x \<otimes> y)) \<longleftrightarrow> w \<preceq> (x \<ominus> y)"
    using product right D_def O_def P_transitivity by smt
  thus "x \<ominus> (x \<otimes> y) = x \<ominus> y"
    using P_antisymmetry P_reflexivity by blast
qed
  
lemma difference_monotonicity: "\<not> x \<preceq> z \<longrightarrow> x \<preceq> y \<longrightarrow> x \<ominus> z \<preceq> y \<ominus> z"
proof
  assume "\<not> x \<preceq> z"
  with strong_supplementation have "\<exists> w. w \<preceq> x \<and> D w z"..
  with difference_character have left: "(\<forall> w. w \<preceq> (x \<ominus> z) \<longleftrightarrow> (w \<preceq> x \<and> D w z))"..
  show "x \<preceq> y \<longrightarrow> x \<ominus> z \<preceq> y \<ominus> z"
  proof
    assume "x \<preceq> y"
    hence "\<not> y \<preceq> z"
      using \<open>\<not> x \<preceq> z\<close> P_transitivity by blast
    with strong_supplementation have "\<exists> w. w \<preceq> y \<and> D w z"..
    with difference_character have right: "(\<forall> w. w \<preceq> (y \<ominus> z) \<longleftrightarrow> (w \<preceq> y \<and> D w z))"..
    hence "\<forall> w. w \<preceq> (x \<ominus> z) \<longrightarrow> w \<preceq> (y \<ominus> z)"
      using P_transitivity \<open>x \<preceq> y\<close> left by blast
    thus "x \<ominus> z \<preceq> y \<ominus> z"
      using P_reflexivity by auto
  qed
qed

end

section {* Closed Extensional Mereology with Complements *}

locale closure_mereology_with_complements = closure_mereology +
  assumes complement_closure: "\<not> (\<forall> y. y \<preceq> x) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x)"

begin

lemma conditional_complement_character: "\<not> (\<forall> y. y \<preceq> x) \<longrightarrow> (\<forall> w. w \<preceq> (\<midarrow> x) \<longleftrightarrow> D w x)"
proof
  assume "\<not> (\<forall> y. y \<preceq> x)"
  with complement_closure have "\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x"..
  then obtain a where a: "\<forall> w. w \<preceq> a \<longleftrightarrow> D w x"..
  hence "(THE z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x) = a"
  proof (rule the_equality)
    show "\<And>z. \<forall>w. (w \<preceq> z) = D w x \<Longrightarrow> z = a"
      using a P_antisymmetry P_reflexivity by blast
  qed
  hence "(\<midarrow> x) = a"
    using complement_def by auto
  thus "(\<forall> w. w \<preceq> (\<midarrow> x) \<longleftrightarrow> D w x)"
    by (simp add: a)
qed

lemma complement_overlap: "D x y \<longrightarrow> O x (\<midarrow> y)"
  using conditional_complement_character D_def P_implies_O by blast

lemma difference_closure: "(\<exists> w. w \<preceq> x \<and> D w y) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y))"
proof
  assume antecedent: "(\<exists> w. w \<preceq> x \<and> D w y)"
  hence "\<not> (\<forall> z. z \<preceq> y)"
    using D_def P_implies_O by blast
  with conditional_complement_character have comp: "\<forall> w. w \<preceq> (\<midarrow> y) \<longleftrightarrow> D w y"..
  hence "O x (\<midarrow> y)"
    by (simp add: antecedent O_def)
  with product_character have "\<forall> w. w \<preceq> x \<otimes> \<midarrow> y \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> \<midarrow> y"..
  hence "\<forall> w. w \<preceq> x \<otimes> \<midarrow> y \<longleftrightarrow> w \<preceq> x \<and> D w y"
    using comp by blast
  thus "\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> D w y)"..
qed

end

sublocale closure_mereology_with_complements \<subseteq> closure_mereology_with_differences
  by (simp add: closure_mereology_axioms closure_mereology_with_differences.intro
closure_mereology_with_differences_axioms.intro difference_closure)

locale closed_extensional_mereology_with_complements = closed_extensional_mereology +
  closure_mereology_with_complements

begin

lemma complement_as_sum: "x \<noteq> u \<longrightarrow> (\<sigma> z. D x z) = \<midarrow> x"
proof
  assume "x \<noteq> u"
  hence "\<not> (\<forall> y. y \<preceq> x)"
    using u_intro by blast
  with conditional_complement_character have "\<forall> w. (w \<preceq> \<midarrow> x) \<longleftrightarrow> D w x"..
  hence "\<forall> y. O y (\<midarrow> x) \<longleftrightarrow> (\<exists> z. (D x z) \<and> O z y)"
    by (meson D_symmetry O_symmetry P_iff_all_O_O)
  with fusion_intro show "(\<sigma> z. D x z) = \<midarrow> x"..
qed

end

locale closed_extensional_mereology_with_universe_and_complements =
closed_extensional_mereology_with_universe + closed_extensional_mereology_with_complements 

begin

lemma complement_character: "x \<noteq> u \<longrightarrow> (\<forall> w. w \<preceq> (\<midarrow> x) \<longleftrightarrow> D w x)"
  using conditional_complement_character u_intro by blast

lemma unique_complement: "(\<exists>! z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x) \<longleftrightarrow> x \<noteq> u"
proof
  assume  "(\<exists>! z. \<forall> w.  w \<preceq> z \<longleftrightarrow> D w x)"
  thus "x \<noteq> u"
    by (meson D_def P_reflexivity P_implies_O u_character)
next
  assume "x \<noteq> u"
  show "\<exists>! z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x"
  proof
    show "\<forall> w. (w \<preceq> \<midarrow> x) \<longleftrightarrow> D w x"
      using \<open>x \<noteq> u\<close> complement_character by simp
    show "\<And>z. \<forall>w. (w \<preceq> z) \<longleftrightarrow> D w x \<Longrightarrow> z = \<midarrow> x"
      using complement_intro by simp
  qed
qed

lemma complements_disjoint: "x \<noteq> u \<longrightarrow> D x (\<midarrow> x)"
  using D_symmetry P_reflexivity complement_character by blast

lemma additive_inverse: "x \<noteq> u \<longrightarrow> x \<oplus> (\<midarrow> x) = u"
proof
  assume "x \<noteq> u"
  with complement_character have "(\<forall> w. w \<preceq> (\<midarrow> x) \<longleftrightarrow> D w x)"..
  have "\<forall> w. O w (x \<oplus> (\<midarrow> x)) \<longleftrightarrow> (O w x \<or> O w (\<midarrow> x))" using sum_character.
  thus "(x \<oplus> (\<midarrow> x)) = u"
    by (metis \<open>\<forall>w. (w \<preceq> \<midarrow> x) = D w x\<close> D_def P_iff_all_O_O P_implies_O u_intro)
qed

lemma in_comp_iff_disjoint: "y \<noteq> u \<longrightarrow> x \<preceq> \<midarrow> y \<longleftrightarrow> D x y"
  by (simp add: complement_character)

lemma double_complement: "x \<noteq> u \<longrightarrow> x = (\<midarrow>(\<midarrow> x))"
  by (metis additive_inverse complements_disjoint D_irreflexive summand_part first_summand_inclusion
P_antisymmetry complement_character)

lemma overlaps_relative_complement: "O w x \<and> O x y \<and> O x (\<midarrow>y) \<longrightarrow> D w (x \<otimes> y) \<longrightarrow> O w (x \<otimes> (\<midarrow>y))"
proof
  assume antecedent: "O w x \<and> O x y \<and> O x (\<midarrow> y)"
  hence "O w x"..
  with product_character have prodwx: "(\<forall> v. v \<preceq> (w \<otimes> x) \<longleftrightarrow> (v \<preceq> w \<and> v \<preceq> x))"..
  have "O x (\<midarrow> y)"
    using antecedent by blast
  with product_character have prod_comp: "(\<forall> w. w \<preceq> (x \<otimes> (\<midarrow> y)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> (\<midarrow> y)))"..
  from antecedent have "O x y" by blast
  with product_character have prodxy: "(\<forall> w. w \<preceq> (x \<otimes> y) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"..
  show "D w (x \<otimes> y) \<longrightarrow> O w (x \<otimes> (\<midarrow>y))"
  proof
    assume D: "D w (x \<otimes> y)"
    hence "y \<noteq> u"
      using antecedent D_def multiplicative_identity by auto
    with complement_character have comp: "\<forall> w. w \<preceq> (\<midarrow> y) \<longleftrightarrow> D w y"..
    hence "w \<otimes> x \<preceq> x \<otimes> (\<midarrow> y)" using prodwx prodxy
      using antecedent D D_def O_def in_second_factor prod_comp by auto
    hence "w \<otimes> x \<preceq> w \<and> w \<otimes> x \<preceq> x \<otimes> (\<midarrow> y)"
      by (simp add: antecedent in_first_factor)
    thus "O w (x \<otimes> (\<midarrow>y))"
      using O_def by blast
  qed
qed

lemma redundancy:
"y \<noteq> u \<and> O x y \<and> \<not> x \<preceq> y \<longrightarrow> x = ((x \<otimes> y) \<oplus> (x \<otimes> (\<midarrow>y)))"
proof
  assume antecedent: "y \<noteq> u \<and> O x y \<and> \<not> x \<preceq> y"
  hence "y \<noteq> u"..
  with complement_character have comp: "(\<forall> w. w \<preceq> (\<midarrow> y) \<longleftrightarrow> D w y)"..
  hence "O x (\<midarrow> y)"
    by (simp add: antecedent O_def strong_supplementation)
  with product_character have prod_comp: "\<forall> w. w \<preceq> x \<otimes> (\<midarrow> y) \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> (\<midarrow> y)"..
  from antecedent have "O x y \<and> \<not> x \<preceq> y"..
  hence "O x y"..
  with product_character have prod: "\<forall> w. w \<preceq> x \<otimes> y \<longleftrightarrow> w \<preceq> x \<and> w \<preceq> y"..
  from sum_character have "\<forall>w. O w ((x \<otimes> y) \<oplus> (x \<otimes> (\<midarrow>y))) \<longleftrightarrow> (O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y)))".
  have "\<forall> w. O w x \<longleftrightarrow> O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"
  proof
    fix w
    show "O w x \<longleftrightarrow> O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"
    proof
      assume "O w x"
      with product_character have product: "\<forall> v. v \<preceq> w \<otimes> x \<longleftrightarrow> v \<preceq> w \<and> v \<preceq> x"..
      show "O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"
      proof cases
        assume "O w (x \<otimes> y)"
        thus "O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"..
      next
        assume "\<not> O w (x \<otimes> y)"
        hence "O w (x \<otimes> (\<midarrow> y))"
          by (simp add: \<open>O w x\<close> \<open>O x (\<midarrow> y)\<close> antecedent D_def overlaps_relative_complement)
        thus "O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"..
      qed
    next
      assume "O w (x \<otimes> y) \<or> O w (x \<otimes> (\<midarrow>y))"
      thus "O w x"
      proof (rule disjE)
        assume "O w (x \<otimes> y)"
        thus "O w x"
          using \<open>O x y\<close> closure_mereology.product_overlap closure_mereology_axioms by blast
      next
        assume "O w (x \<otimes> (\<midarrow>y))"
        thus "O w x"
          using \<open>O x (\<midarrow> y)\<close> closure_mereology.product_overlap closure_mereology_axioms by blast
      qed
    qed
  qed
  thus " x = ((x \<otimes> y) \<oplus> (x \<otimes> (\<midarrow>y)))"
    using sum_intro O_extensionality by force
qed

lemma disjoint_difference_absorption: "D x y \<longrightarrow> (x \<oplus> y) \<ominus> x = y"
proof
  assume "D x y"
  hence "y \<preceq> (x \<oplus> y) \<and> D y x"
    by (simp add: D_symmetry second_summand_inclusion)
  hence  "(\<exists> w. w \<preceq> (x \<oplus> y) \<and> D w x)"..
  with difference_character have "(\<forall> w. w \<preceq> ((x \<oplus> y) \<ominus> x) \<longleftrightarrow> (w \<preceq> (x \<oplus> y) \<and> D w x))"..
  thus "(x \<oplus> y) \<ominus> x = y"
    by (metis \<open>y \<preceq> x \<oplus> y \<and> D y x\<close> summand_part sum_commutative
P_antisymmetry P_reflexivity)
qed

end

locale closed_extensional_mereology_with_universe_and_differences =
closed_extensional_mereology_with_universe + closed_extensional_mereology_with_differences

begin

lemma complement_closure: "\<not> (\<forall> y. y \<preceq> x) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x)"
proof
  assume "\<not> (\<forall> y. y \<preceq> x)"
  hence "\<exists> w. w \<preceq> u \<and> D w x"
    using strong_supplementation u_character by blast
  with difference_character have "\<forall> w. w \<preceq> u \<ominus> x \<longleftrightarrow> w \<preceq> u \<and> D w x"..
  hence "\<forall> w. w \<preceq> u \<ominus> x \<longleftrightarrow> D w x"
    by (simp add: u_character)
  thus "\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x"..
qed

end

sublocale closed_extensional_mereology_with_universe_and_differences \<subseteq>
  closed_extensional_mereology_with_universe_and_complements
proof
  show "\<And> x. \<not> (\<forall> y. y \<preceq> x) \<longrightarrow> (\<exists> z. \<forall> w. (w \<preceq> z) \<longleftrightarrow> D w x)"
    using complement_closure by simp
qed

section {* General Mereology *}

text {* General Mereology is obtained from Ground Mereology by adding the axiom of fusion or
unrestricted composition @{cite "casati_Parts_1999"} p. 46:  *}

locale general_mereology = ground_mereology +
  assumes fusion: "(\<exists> x. F x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
-- "fusion or unrestricted composition"

begin
 
lemma sum_closure: "(\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w a \<or> O w b))"
proof -
  have "(\<exists> x. (x = a \<or> x = b)) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O x y))"
    using fusion solve_direct.
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. (x = a \<or> x = b) \<and> O x y))"
    by blast
  thus "(\<exists>z. \<forall>w. O w z \<longleftrightarrow> (O w a \<or> O w b))"
    by (metis O_symmetry) 
qed

lemma something_everything_overlaps: "\<exists> z. \<forall> x. O x z"
proof -
  have "(\<exists> x. x = x) \<longrightarrow> (\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. x = x \<and> O x y))"
    using fusion by fast
  hence  "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. x = x \<and> O x y)"
    by simp
  hence  "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. O x y)"
    by simp
  thus ?thesis
    by (metis O_def P_reflexivity)
qed

end

locale general_minimal_mereology = minimal_mereology + general_mereology -- "General Minimal Mereology"

subsection {* Classical Extensional Mereology *}

locale classical_extensional_mereology = extensional_mereology + general_mereology
begin

text {* The following proofs are adapted from Colin Pontow @{cite "pontow_note_2004"} pp. 202-9: *}

lemma fusion_character: "(\<exists> x. F x) \<longrightarrow> (\<forall> y. y \<preceq> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w)))"
proof
  assume "(\<exists> x. F x)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  with fusion_intro have sum:  "(\<sigma> v. F v) = z "..
  show "\<forall> y. y \<preceq> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
  proof
    fix y
    show "y \<preceq> (\<sigma> v. F v) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
    proof
      assume "y \<preceq> (\<sigma> v. F v)"
      hence "y \<preceq> z"
        using sum by simp
      hence "O y z"
        using O_def P_reflexivity by auto
      hence "(\<exists> x. F x \<and> O x y)"
        using z by simp
      thus "(\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
        by (metis O_def P_reflexivity P_transitivity \<open>y \<preceq> z\<close> z)
    next
      assume "(\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"
      hence "y \<preceq> z" using z
        by (meson D_def strong_supplementation)
      thus "y \<preceq> (\<sigma> v. F v)"
        using sum by simp
    qed
  qed
qed

lemma product_closure: "O x y \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"
proof
  assume "O x y"
  hence common_P: "\<exists> z. (z \<preceq> x \<and> z \<preceq> y)"
    using O_def by simp
  have "(\<exists> v. (v \<preceq> x \<and> v \<preceq> y)) \<longrightarrow> (\<forall> w. w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y))  \<longleftrightarrow> (\<forall> z. z \<preceq> w \<longrightarrow> (\<exists> v. (v \<preceq> x \<and> v \<preceq> y) \<and> O v z)))"
    using fusion_character.
  hence common_P_sum: "(\<forall> w. w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y)) \<longleftrightarrow> (\<forall> z. z \<preceq> w \<longrightarrow> (\<exists> v. (v \<preceq> x \<and> v \<preceq> y) \<and> O v z)))"
    using common_P..
  have "\<forall> w. w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"
  proof
    fix w
    show "w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y)) \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y)"
    proof
      assume "w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y))"
      hence "(\<forall> t. t \<preceq> w \<longrightarrow> (\<exists> v. v \<preceq> x \<and> v \<preceq> y \<and> O v t))"
        using common_P_sum by simp
      hence "\<forall> t. t \<preceq> w \<longrightarrow> (O t x \<and> O t y)"
        by (meson O_symmetry P_iff_all_O_O)
      thus "w \<preceq> x \<and> w \<preceq> y"
        using strong_supplementation P_transitivity D_def by meson
    next
      assume "w \<preceq> x \<and> w \<preceq> y"
      thus "w \<preceq> (\<sigma> v. (v \<preceq> x \<and> v \<preceq> y))"
        using O_def P_reflexivity common_P_sum by fastforce
    qed
  qed
  thus "(\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> x \<and> w \<preceq> y))"..
qed

lemma universe_closure: "\<exists> z. \<forall> x. x \<preceq> z"
  using D_def something_everything_overlaps strong_supplementation by blast

lemma difference_closure: "(\<exists> w. w \<preceq> a \<and> D w b) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> a \<and> D w b))"
proof
  assume antecedent: "(\<exists> w. w \<preceq> a \<and> D w b)"
  have "(\<exists> x. (x \<preceq> a \<and> D x b)) \<longrightarrow> (\<forall> y. y \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b)) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. (v \<preceq> a \<and> D v b) \<and> O v w)))"
    using fusion_character.
  hence sum: "\<forall> y. y \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b)) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. (v \<preceq> a \<and> D v b) \<and> O v w))"
    using antecedent..
  have "\<forall> w. w \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b)) \<longleftrightarrow> (w \<preceq> a \<and> D w b)"
  proof
    fix w
    show "w \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b)) \<longleftrightarrow> (w \<preceq> a \<and> D w b)"
    proof
      assume left: "w \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b))"
      have "\<forall> z. z \<preceq> w \<longrightarrow> O z a"
        using left O_symmetry P_iff_all_O_O sum by blast
      hence "w \<preceq> a"
        using strong_supplementation D_def by blast
      have "\<forall> v. v \<preceq> w \<longrightarrow> \<not> v \<preceq> b"
        by (metis O_def D_def P_transitivity sum left)
      hence "D w b"
        using O_def D_def by simp
      with \<open>w \<preceq> a\<close> show "w \<preceq> a \<and> D w b"..
    next
      assume "w \<preceq> a \<and> D w b"
      thus "w \<preceq> (\<sigma> v. (v \<preceq> a \<and> D v b))"
        using O_symmetry P_implies_O sum by blast
    qed
  qed
  thus "(\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> (w \<preceq> a \<and> D w b))"..
qed

lemma complement_closure: "(\<exists> w. D w x) \<longrightarrow> (\<exists> z. \<forall> w. w \<preceq> z \<longleftrightarrow> D w x)"
  by (meson difference_closure universe_closure)

end

sublocale classical_extensional_mereology \<subseteq> closed_extensional_mereology_with_universe_and_differences
proof (unfold_locales)
  show "\<And>x y. U x y \<longrightarrow> (\<exists>z. \<forall>w. O w z = (O w x \<or> O w y))" using sum_closure by simp
  show " \<And>x y. O x y \<longrightarrow> (\<exists>z. \<forall>w. (w \<preceq> z) = (w \<preceq> x \<and> w \<preceq> y))" using product_closure.
  show "\<exists>z. \<forall>x. x \<preceq> z" using universe_closure.
  show "\<And>x y. (\<exists>w. w \<preceq> x \<and> D w y) \<longrightarrow> (\<exists>z. \<forall>w. (w \<preceq> z) = (w \<preceq> x \<and> D w y))" using difference_closure.
qed

context classical_extensional_mereology
begin

(*
text {* These two lemmas from Simons appear to be mistakes: *}
lemma SCT60: "(\<exists> y. x \<prec> y) \<longrightarrow> x = (\<pi> z. x \<prec> z)" nitpick [user_axioms] oops
lemma SCT61:
"(\<exists> x. F x) \<longrightarrow> (\<exists> x. \<forall> y. F y \<longrightarrow> x \<preceq> y) \<longrightarrow> (\<pi> x. F x) = (THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> y \<preceq> z))" nitpick [user_axioms] oops
*)

lemma strong_fusion: "(\<exists> x. F x) \<longrightarrow> (\<exists> x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. y \<preceq> x \<longrightarrow> (\<exists> z. F z \<and> O y z)))"
proof
  assume "(\<exists> x. F x)"
  with fusion_character have sum_F: "\<forall> y. (y \<preceq> (\<sigma> v. F v)) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists>v. F v \<and> O v w))"..
  hence "(\<forall> y. F y \<longrightarrow> y \<preceq> (\<sigma> v. F v)) \<and> (\<forall> y. y \<preceq> (\<sigma> v. F v) \<longrightarrow> (\<exists>z. F z \<and> O y z))"
    by (meson P_implies_O P_reflexivity O_symmetry)
  thus "(\<exists> x. (\<forall>y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. y \<preceq> x \<longrightarrow> (\<exists>z. F z \<and> O y z)))"..
qed

lemma strong_fusion_character: 
"(\<exists> x. F x) \<longrightarrow> (\<forall> y. F y \<longrightarrow> y \<preceq> (\<rho> x. F x)) \<and> (\<forall> y. y \<preceq> (\<rho> x. F x) \<longrightarrow> (\<exists> z. F z \<and> O y z))"
proof
  assume "\<exists> x. F x"
  with strong_fusion have "\<exists> x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. y \<preceq> x \<longrightarrow> (\<exists> z. F z \<and> O y z))"..
  then obtain x where x: "(\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. y \<preceq> x \<longrightarrow> (\<exists> z. F z \<and> O y z))"..
  with strong_fusion_intro have "(\<rho> v. F v) = x"..
  thus "(\<forall> y. F y \<longrightarrow> y \<preceq> (\<rho> x. F x)) \<and> (\<forall> y. y \<preceq> (\<rho> x. F x) \<longrightarrow> (\<exists> z. F z \<and> O y z))"
    using x by metis
qed

lemma fusion_is_strong_fusion: "(\<exists> x. F x) \<longrightarrow> (\<sigma> x. F x) = (\<rho> x. F x)" 
proof
  assume exists_F: "(\<exists> x. F x)"
  with fusion_character have sum_F: "\<forall> y. (y \<preceq> (\<sigma> v. F v)) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists>v. F v \<and> O v w))"..
  have strong_sum_F: "(\<forall> y. F y \<longrightarrow> y \<preceq> (\<rho> x. F x)) \<and> (\<forall>y. y \<preceq> (\<rho> x. F x) \<longrightarrow> (\<exists>z. F z \<and> O y z))"
    using exists_F strong_fusion_character by simp
  thus "(\<sigma> x. F x) = (\<rho> x. F x)"
  proof -
    have "(\<sigma> x. F x) = (THE x. \<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O z y))"
      using fusion_def by simp
    also have "... = (\<rho> x. F x)"
    proof
      show existence: "\<forall> y. O y (\<rho> x. F x) \<longleftrightarrow> (\<exists>z. F z \<and> O z y)"
        by (meson O_def P_transitivity strong_sum_F)
      show uniqueness: "\<And> x. \<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O z y) \<Longrightarrow> x = (\<rho> x. F x)"
      proof -
        fix x
        show "\<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O z y) \<Longrightarrow> x = (\<rho> x. F x)"
        proof -
          assume "\<forall>y. O y x \<longleftrightarrow> (\<exists>z. F z \<and> O z y)"
          thus "x = (\<rho> x. F x)" using strong_sum_F
            by (metis existence P_antisymmetry P_iff_all_O_O)
        qed
      qed
    qed
    finally show "(\<sigma> x. F x) = (\<rho> x. F x)"
      by simp
  qed
qed

lemma fusion_part_def: "(\<exists> x. F x) \<longrightarrow> (\<sigma> x. F x) = (THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y))"
proof
  assume "\<exists> x. F x"
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> x. F x) = z"
    using fusion_intro by simp
  have "(THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y)) = z"
  proof (rule the_equality)
    show "\<forall>y. z \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y)"
    proof
      fix y
      show "z \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y)"
      proof
        assume "z \<preceq> y" 
        thus "(\<forall> z. F z \<longrightarrow> z \<preceq> y)"
          using O_symmetry P_iff_all_O_O z by blast
      next
        assume "(\<forall> z. F z \<longrightarrow> z \<preceq> y)"
        thus "z \<preceq> y"
          using O_symmetry P_iff_all_O_O z by blast
      qed
    qed
    thus "\<And>x. \<forall>y. (x \<preceq> y) = (\<forall>z. F z \<longrightarrow> z \<preceq> y) \<Longrightarrow> x = z"
      using P_antisymmetry P_reflexivity by blast
  qed
  thus "(\<sigma> x. F x) = (THE x. \<forall> y. x \<preceq> y \<longleftrightarrow> (\<forall> z. F z \<longrightarrow> z \<preceq> y))" 
    using \<open>(\<sigma> x. F x) = z\<close> by metis
qed

lemma fusion_overlap_def:
"(\<exists> x. F x) \<longrightarrow> (\<sigma> x. F x) = (THE x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z)))"
proof
  assume "\<exists> x. F x"
  hence "(\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y))"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "z = (\<sigma> x. F x)"
    using fusion_intro by simp
  have "(THE x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z))) = z"
  proof (rule the_equality)
    show "(\<forall>y. F y \<longrightarrow> y \<preceq> z) \<and> (\<forall>y. O y z = (\<exists>z. F z \<and> O y z))"
      using O_symmetry P_iff_all_O_O z by blast
    thus " \<And>x. (\<forall>y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall>y. O y x = (\<exists>z. F z \<and> O y z)) \<Longrightarrow> x = z"
      by (metis sum_intro)
  qed
  thus "(\<sigma> x. F x) = (THE x. (\<forall> y. F y \<longrightarrow> y \<preceq> x) \<and> (\<forall> y. O y x \<longleftrightarrow> (\<exists> z. F z \<and> O y z)))" 
    using \<open>z = (\<sigma> x. F x)\<close> by metis
qed

lemma fusion_overlap: "(\<exists> y. F y) \<longrightarrow> O x (\<sigma> y. F y) \<longleftrightarrow> (\<exists> z. F z \<and> O z x)"
proof
  assume "(\<exists> y. F y)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> y. F y) = z"
    using fusion_intro by simp
  thus "O x (\<sigma> y. F y) \<longleftrightarrow> (\<exists> z. F z \<and> O z x)" by (metis z)
qed

lemma fusion_disjointness: "D x (\<sigma> y. F y) \<longrightarrow> (\<forall> z. F z \<longrightarrow> D z x)"
proof
  assume antecedent: "D x (\<sigma> y. F y)"
  show "(\<forall> z. F z \<longrightarrow> D z x)"
  proof cases
    assume "\<exists> z. F z"
    with fusion_character have sum: "\<forall> y. (y \<preceq> (\<sigma> v. F v)) \<longleftrightarrow> (\<forall> w. w \<preceq> y \<longrightarrow> (\<exists> v. F v \<and> O v w))"..
    show "(\<forall> z. F z \<longrightarrow> D z x)"
    proof
      fix z
      show "F z \<longrightarrow> D z x"
      proof
        assume "F z"
        from sum have "(z \<preceq> (\<sigma> v. F v)) \<longleftrightarrow> (\<forall> w. w \<preceq> z \<longrightarrow> (\<exists> v. F v \<and> O v w))"..
        with \<open>F z\<close> have "(z \<preceq> (\<sigma> v. F v))"
          by (metis O_symmetry P_reflexivity P_iff_all_P_O)
        with antecedent show "D z x" 
          by (metis D_def O_symmetry P_iff_all_O_O)
      qed
    qed
  next
    assume "\<not> (\<exists> z. F z)"
    thus "\<forall> z. F z \<longrightarrow> D z x"
      by blast
  qed
qed

lemma "(\<exists> x. F x) \<and> (\<exists> x. G x) \<longrightarrow>
 (\<sigma> x. F x) \<preceq> (\<sigma> y. G y) \<longrightarrow> (\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))"
proof
  assume "(\<exists> x. F x) \<and> (\<exists> x. G x)"
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. F x \<and> O x y)"..
  hence "(\<sigma> y. F y) = z"
    using fusion_intro by simp
  have "(\<exists> x. G x)"
    by (simp add: \<open>(\<exists>x. F x) \<and> (\<exists>x. G x)\<close>)
  hence "\<exists> z. \<forall> y. O y z \<longleftrightarrow> (\<exists> x. G x \<and> O x y)"
    using fusion by simp
  then obtain z where z: "\<forall> y. O y z \<longleftrightarrow> (\<exists> x. G x \<and> O x y)"..
  hence "(\<sigma> y. G y) = z"
    using fusion_intro by simp
  show "(\<sigma> x. F x) \<preceq> (\<sigma> y. G y) \<longrightarrow> (\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))"
  proof
    assume "(\<sigma> x. F x) \<preceq> (\<sigma> y. G y)"
    thus "(\<forall> x. F x \<longrightarrow> (\<exists> y. G y \<and> O x y))"
      by (metis fusion_disjointness \<open>(\<sigma> y. G y) = z\<close> D_def O_symmetry P_iff_all_O_O P_implies_O z)
  qed
qed

end

end