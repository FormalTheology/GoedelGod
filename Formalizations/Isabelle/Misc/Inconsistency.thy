theory Inconsistency
imports Main "../QML"

begin
section {* Investigation of Goedel's Inconsistency *}

  abbreviation mFalse :: "\<sigma>" where "mFalse \<equiv> (\<lambda>w. (\<exists>(\<lambda>p. p m\<and> m\<not> p)) w)"

  lemma dia_box_false_leads_to_false: "[(mdia (mbox mFalse))] \<longrightarrow> [mFalse]"
  sledgehammer [provers = remote_leo2]
  nitpick [satisfy]
  by meson 

  lemma dia_box_false_implies_false: "[(mdia (mbox mFalse)) m\<rightarrow> mFalse]"
  nitpick oops
end
