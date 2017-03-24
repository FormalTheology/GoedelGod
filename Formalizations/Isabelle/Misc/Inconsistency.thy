theory Inconsistency
imports Main "../QML"

begin
section {* Investigation of Goedel's Inconsistency *}

  abbreviation mFalse :: "\<sigma>" where "mFalse \<equiv> (\<lambda>w. (\<^bold>\<exists>p.( p \<^bold>\<and> \<^bold>\<not> p)) w)"

  lemma dia_box_false_leads_to_false: "\<lfloor>(\<^bold>\<diamond> (\<^bold>\<box> mFalse))\<rfloor> \<longrightarrow> \<lfloor>mFalse\<rfloor>"
(*  sledgehammer [provers = remote_leo2]
  nitpick [satisfy]*)
  by meson 

  lemma dia_box_false_implies_false: "\<lfloor>(\<^bold>\<diamond>   (\<^bold>\<box> mFalse)) \<^bold>\<rightarrow> mFalse\<rfloor>"
  nitpick oops
end
