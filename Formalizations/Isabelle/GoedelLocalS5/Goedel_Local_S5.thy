theory Goedel_Local_S5 imports Main 
begin
 declare [[smt_solver = cvc4]]

  typedecl i -- "type for possible worlds" 
  typedecl \<mu> -- "type for individuals"      
  consts r :: "i\<Rightarrow>i \<Rightarrow>bool" (infixr"r"70)     
             -- "accessibility relation r"   
  type_synonym \<sigma> = "(i\<Rightarrow>bool)"

 abbreviation mneg :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<not>_"[52]53) 
  where "\<^bold>\<not>\<phi> \<equiv> \<lambda>w. \<not>\<phi>(w)" 
 abbreviation mnegpred :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>(\<mu>\<Rightarrow>\<sigma>)" ("\<^sup>\<not>_"[52]53) 
  where "\<^sup>\<not>\<Phi> \<equiv> \<lambda>x.\<lambda>w. \<not>\<Phi>(x)(w)"  
 abbreviation mand :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<and>"51) 
  where "\<phi>\<^bold>\<and>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<and>\<psi>(w)"   
 abbreviation mor  :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<or>"50) 
  where "\<phi>\<^bold>\<or>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<or>\<psi>(w)"   
 abbreviation mimpl :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<rightarrow>"49) 
  where "\<phi>\<^bold>\<rightarrow>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longrightarrow>\<psi>(w)"  
 abbreviation mequiv :: "\<sigma>\<Rightarrow>\<sigma>\<Rightarrow>\<sigma>" (infixr"\<^bold>\<equiv>"48) 
  where "\<phi>\<^bold>\<equiv>\<psi> \<equiv> \<lambda>w. \<phi>(w)\<longleftrightarrow>\<psi>(w)"  
 abbreviation mall :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<forall>") 
  where "\<^bold>\<forall>\<Phi> \<equiv> \<lambda>w.\<forall>x. \<Phi>(x)(w)"
 abbreviation mallB:: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<forall>"[8]9) 
  where "\<^bold>\<forall>x. \<phi>(x) \<equiv> \<^bold>\<forall>\<phi>"   
 abbreviation mexi :: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" ("\<^bold>\<exists>") 
  where "\<^bold>\<exists>\<Phi> \<equiv> \<lambda>w.\<exists>x. \<Phi>(x)(w)"
 abbreviation mexiB:: "('a\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" (binder"\<^bold>\<exists>"[8]9) 
  where "\<^bold>\<exists>x. \<phi>(x) \<equiv> \<^bold>\<exists>\<phi>"   
 abbreviation mbox :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<box>") 
  where "\<^bold>\<box>\<phi> \<equiv> \<lambda>w. \<forall>v.  w r v \<longrightarrow> \<phi> v"
 abbreviation mdia :: "\<sigma>\<Rightarrow>\<sigma>" ("\<^bold>\<diamond>") 
  where "\<^bold>\<diamond>\<phi> \<equiv> \<lambda>w. \<exists>v. w r v \<and> \<phi> v" 

 abbreviation valid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>"[7]8) 
  where "\<lfloor>p\<rfloor> \<equiv> \<forall>w. p w"

(* Local validity of a (higher-order) modal logic formula means truth
   with respect to the current world *)
 consts cw :: i 

 abbreviation mlocalvalid :: "\<sigma> \<Rightarrow> bool" ("\<lfloor>_\<rfloor>\<^sup>c\<^sup>w"[7]8) 
  where "\<lfloor>p\<rfloor>\<^sup>c\<^sup>w \<equiv> p cw"


  consts P :: "(\<mu>\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>"                                     (* Positive *)

  axiomatization where 
(* A1: Either a property or its negation is positive, but not both *)
   A1a: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<^sup>\<not>\<Phi>) \<^bold>\<rightarrow> \<^bold>\<not>P(\<Phi>)\<rfloor>\<^sup>c\<^sup>w" and 
   A1b: "\<lfloor>\<^bold>\<forall>\<Phi>. \<^bold>\<not>P(\<Phi>) \<^bold>\<rightarrow> P(\<^sup>\<not>\<Phi>)\<rfloor>\<^sup>c\<^sup>w" and 
(* A2: A property necessarily implied by a positive property is positive *)
   A2: "\<lfloor>\<^bold>\<forall>\<Phi> \<Psi>. P(\<Phi>) \<^bold>\<and> \<^bold>\<box>(\<^bold>\<forall>x. \<Phi>(x) \<^bold>\<rightarrow> \<Psi>(x)) \<^bold>\<rightarrow> P(\<Psi>)\<rfloor>\<^sup>c\<^sup>w"

(* T1: Positive properties are possibly exemplified *)
 theorem T1: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists>x. \<Phi>(x))\<rfloor>\<^sup>c\<^sup>w" using A1a A2 by blast

(* God: A God-like being possesses all positive properties *)
 definition G where "G(x) = (\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<Phi>(x))"   

(* A3: The property of being God-like is positive *)
 axiomatization where A3: "\<lfloor>P(G)\<rfloor>\<^sup>c\<^sup>w"

(* C: Possibly, God exists *) 
 corollary C: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>x. G(x))\<rfloor>\<^sup>c\<^sup>w" by (metis A3 T1)

(* A4: Positive properties are necessarily positive *)
 axiomatization where A4: "\<lfloor>\<^bold>\<forall>\<Phi>. P(\<Phi>) \<^bold>\<rightarrow> \<^bold>\<box>(P(\<Phi>))\<rfloor>\<^sup>c\<^sup>w" 

(* Ess: An essence of an individual is a property possessed by 
        it and necessarily implying any of its properties: *)
 definition ess (infixr "ess" 85) where
    "\<Phi> ess x = (\<^bold>\<forall>\<Psi>. \<Psi>(x) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>y. \<Phi>(y) \<^bold>\<rightarrow> \<Psi>(y)))"

(* T2: Being God-like is an essence of any God-like being *)
 theorem T2: "\<lfloor>\<^bold>\<forall>x. G(x) \<^bold>\<rightarrow> G ess x\<rfloor>\<^sup>c\<^sup>w" by (smt A1b A4 G_def ess_def)

(* NE: Necessary existence of an individual is the necessary 
       exemplification of all its￼essences *)
 definition NE where "NE(x) = (\<^bold>\<forall>\<Phi>. \<Phi> ess x \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists>x. \<Phi>(x)))"

(* A5: Necessary existence is a positive property *)
 axiomatization where A5:  "\<lfloor>P(NE)\<rfloor>\<^sup>c\<^sup>w"

 axiomatization where sym: "x r y \<longrightarrow> y r x" 


(* Consistency is confirmed by Nitpick *)
 lemma True nitpick [satisfy, user_axioms] oops  


 lemma False 
  (* sledgehammer [provers = remote_leo2,verbose] *) (* LEO-II can prove this *)
  proof -
   have   "\<lfloor>\<^bold>\<forall>x. (\<lambda>x w. \<not>(x = x)) ess x\<rfloor>\<^sup>c\<^sup>w" by (simp add: ess_def)
   thus ?thesis by (smt A4 A5 C G_def sym NE_def ess_def)
  qed

  (* Note that only symmetry is needed for the inconsistency *)
end