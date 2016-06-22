theory Satan_S5U imports Scott_S5U 
begin 

 definition D where "D(x) = (\<^bold>\<forall>\<Phi>. \<^bold>\<not>P(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"   (* Definition of Devil *)

 lemma T3D: "\<lfloor>\<^bold>\<box> (\<^bold>\<exists> D)\<rfloor>"  (* Necessarily, the Devil exists *)
   nitpick [user_axioms = true]  (* Nitpick finds a counter-model *)
   (* nitpick [user_axioms = true, satisfy] *) (* Nitpick does not find a model *)
   oops

 lemma T3ND: "\<lfloor> \<^bold>\<not> ( \<^bold>\<box> (\<^bold>\<exists> D) ) \<rfloor>"
   (* nitpick *)  (* Nitpick does not find a counter-model *)
   nitpick [user_axioms = true, satisfy] (* Nitpick finds a model *)
   sledgehammer [provers = remote_leo2 remote_satallax] (* leo2  finds a proof *)
   by (metis (no_types, lifting) A1a A4 A5 D_def NE_def ess_def) (* metis finds a proof *)

 lemma T3ND3: "\<lfloor> \<^bold>\<not> (\<^bold>\<exists> D) \<rfloor>" 
   (* nitpick *)  (* Nitpick does not find a counter-model *)
   nitpick [user_axioms = true, satisfy] (* Nitpick finds a model *)
   (* sledgehammer [provers = remote_leo2 remote_satallax remote_vampire] *) (* Sledgehammer runs out of time *)
   oops

 lemma T3ND2: "\<lfloor> \<^bold>\<box> ( \<^bold>\<not> (\<^bold>\<exists> D) ) \<rfloor>"
   (* nitpick *)  (* Nitpick does not find a counter-model *)
   nitpick [user_axioms = true, satisfy] (* Nitpick finds a model *)
   (* sledgehammer [provers = remote_leo2 remote_satallax remote_vampire] *) (* Sledgehammer runs out of time *)
   (* by (metis (no_types, lifting) A1a A1b A2 A3 A4 A5 D_def G_def NE_def T2 ess_def) (* metis does not terminate *) *)
   oops


 (* The analogous of axiom A2 for negative properties is counter-satisfiable  *)
 (* This shows that Goedel's theory is "asymmetric". *) 
 (* It tells us more about positive properties than about negative properties. *)
 lemma A2D:  "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>.  \<^bold>\<not> P(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow>  \<^bold>\<not> P(\<Psi>)\<rfloor>"
   nitpick [user_axioms = true] (* Nitpick finds a counter-model *)
   oops
  
end
