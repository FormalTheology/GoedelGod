theory EquiValidity_S5_S5U imports QML_S5
begin

 abbreviation mboxU :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>u") 
  where "\<^bold>\<box>u \<phi> \<equiv> \<lambda>w.\<forall>v. \<phi>(v)"
 abbreviation mdiaU :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>u") 
  where "\<^bold>\<diamond>u \<phi> \<equiv> \<lambda>w.\<exists>v. \<phi>(v)" 

  theorem test1:  "\<lfloor>(\<^bold>\<box>u \<phi>) \<^bold>\<rightarrow> (\<^bold>\<box> \<phi>)\<rfloor>"
  sledgehammer
  by simp

  theorem test2:  "\<lfloor>(\<^bold>\<box> \<phi>) \<^bold>\<rightarrow> (\<^bold>\<box>u \<phi>)\<rfloor>"
  sledgehammer
  by simp
end
