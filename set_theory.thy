theory set_theory imports ZFC classical_axioms fol_theorems
begin
(* use all *)
context 
  fixes S
  fixes W defines W_def : "W == {x\<in>S. x\<notin>x}"
begin
lemma ex_1_2' : " \<not> ( Pow(S) \<subseteq> S )"
  apply (rule notI)
  apply (rule case_split[where P="W\<in>W"])
  apply (rule notE[where P="W\<in>W"])
    apply (rule CollectD2[where A=S])
    apply (fold W_def)
    apply assumption
   apply assumption
  apply (rule notE[where P="W\<in>W"])
   apply assumption
  apply (unfold W_def)
   apply (rule CollectI)
   apply (fold W_def)
   prefer 2
  apply assumption
  (*subgoal*)
   apply (unfold subset_def)
   apply (unfold Ball_def)
    apply (rule mp[where P="W\<in>Pow(S)"])
     apply (rule spec[where x=W])
     apply assumption
    apply (rule PowI)
    apply (unfold W_def)
    apply (unfold subset_def)
    apply (unfold Ball_def)
    apply (rule allI)
    apply (rule impI)
    apply (rule CollectD1)
    apply assumption
  done
end 

lemma l0:"True"
  apply(rule TrueI)
  done

context 
  fixes S
  fixes W defines W_def : "W == {y. x\<in>S, True }"
begin
 lemma l1 : "W \<subseteq> 0"
  apply(unfold subset_def)
  apply(unfold Ball_def)
  apply(rule allI)
  apply(rule impI)
  apply(unfold W_def)
  apply(rule mp)
   prefer 2
   apply assumption
(*  apply(rule replacement)
   apply(unfold  _Replace)
  replacement:   "(\<forall>x\<in>A. \<forall>y z. P(x,y) \<and> P(x,z) \<longrightarrow> y = z) \<Longrightarrow>
                         b \<in> PrimReplace(A,P) \<longleftrightarrow> (\<exists>x\<in>A. P(x,b))"
we cannot prove (\<forall>x\<in>A. \<forall>y z.  (%a b. True)(x,y) \<and> (%a b. True)(x,z) \<longrightarrow> y = z)
// \<langle>x,y\<rangle>\<notin>0, \<langle>x,y\<rangle> \<notin>(x,z)
*)
  oops
end

lemma l2: \<open>(\<lambda>a b. True)(x,z)\<close>
  apply(rule TrueI)
  done

lemma l3: \<open>S \<subseteq>  {b . a \<in> S, a = b}\<close>
  (* subsetI *)
  apply(unfold subset_def)
  apply(unfold Ball_def)
  apply(rule allI) (* intro *) 
  apply(rule impI) (* intro *)
  apply(rule iffD2)

  (* apply(unfold Replace_def)
   apply(rule replacement)*)
                        
   apply(rule Replace_iff)        
  apply(unfold Bex_def)
  (* ?  apply(rule exI[where x=x])*)
  apply(rule exI)
  apply(rule conjI)
  (* HOWTO instantiate ?x8(x):=x *)
  apply assumption
  apply(rule conjI) (* = split.*)
  apply(rule refl)
  apply(auto)
  done

lemma l4_1:  \<open>P \<longleftrightarrow> P \<and> True\<close>
  apply auto
  done

lemma collect_is_subset: \<open>{a \<in> S . A} \<subseteq> S\<close>
  apply(rule subsetI)
  apply(rule CollectD1)
  apply assumption
  done

lemma l4: \<open>S = {a \<in> S. True}\<close>
  apply(rule iffD2)
  apply(rule extension)
  apply(rule conjI)
  apply(unfold Collect_def)
   apply(rule subst)
    apply(rule Replace_cong)
     apply(rule refl)
(* how to forget assumption? *)
    apply(rule l4_1)
  apply(rule l3)
  apply(fold Collect_def)
  apply(rule collect_is_subset)
  done

(* CollectD1
  apply(rule conj_simps)
\<open>P \<and> True \<longleftrightarrow> P\<close>)
 \<open>P \<and> True \<longleftrightarrow> P\<close>
 True
  apply(rule RepFun_cong)
  apply(rule Collect_cong) *)

end
