theory set_theory imports ZFC classical_axioms fol_theorems
begin

context
  fixes S
  fixes W defines W_def : "W == {x\<in>S. x\<notin>x}"
begin
lemma ex_1_2 : " \<not> ( Pow(S) \<subseteq> S )"
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

lemma l3: \<open>S \<subseteq> {b . a \<in> S, a = b}\<close>
  apply(rule subsetI)
  apply(rule iffD2)
  (* apply(unfold Replace_def)
   apply(rule replacement) *)
   apply(rule Replace_iff)
  apply(unfold Bex_def)
  (* How to specify metavariable with bounded variable?
     apply(rule exI[where x=x])  [of _ x]*)
  apply(rule exI)
  apply(rule conjI)
  (* How to instantiate ?x8(x):=x  ? *)
  apply assumption
  apply(rule conjI) (* = split.*)
  apply(rule refl)
  apply(auto)
  done

(* original theorem has no name, so... *)
lemma l4_1:  \<open>P \<longleftrightarrow> P \<and> True\<close>
  apply auto
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
  apply(rule Collect_subset)
  done

definition Ind :: "i\<Rightarrow>o"
  where Ind_def : "Ind(x) == 0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)"

lemma exmpl : "Ind(Inf)"
  apply(unfold Ind_def, rule infinity)
  done

lemma ex1_3:
  fixes x
  assumes a:"Ind(x)"
  shows "Ind({y\<in>x. y\<subseteq>x})"
proof -
  from a
  have b: "0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)"
    by (unfold Ind_def)
  from b
  have c1:"0 \<in> x" and c2:"(\<forall>y\<in>x. succ(y) \<in> x)"
    by (rule conjunct1, rule conjunct2)
  from c1
  have d:"0 \<in> {y \<in> x . y \<subseteq> x}"
    apply(rule CollectI)
    apply(rule empty_subsetI)
    done
  from c1 and c2
  have e:"(\<forall>y\<in>{y \<in> x . y \<subseteq> x}. succ(y) \<in> {y \<in> x . y \<subseteq> x})"
    apply(unfold Ball_def)
    apply(rule allI, rule impI)
  proof -
    fix k::"i"
    assume f: "0 \<in> x"
     and g:\<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
     and h:\<open>k \<in> {y \<in> x . y \<subseteq> x}\<close>
    show i:"succ(k) \<in> {y \<in> x . y \<subseteq> x}"
    proof -
      from h
      have h1:"k \<in> x" and h2:"k\<subseteq>x"
        apply(rule CollectD1[where A="x"])
        apply(rule CollectD2[where P="\<lambda>w. w\<subseteq>x"])
        apply(rule h)
        done
      from h1 and h2
      have ik:"succ(k) \<in> {y \<in> x . y \<subseteq> x}"
        apply(unfold succ_def)
        apply(fold succ_def)
        apply(rule CollectI[where P="\<lambda>y. y\<subseteq>x"])
         apply(rule mp)
          apply(rule spec[where x="k"])
          apply(rule g)
         apply assumption
        apply(rule subsetI)
      proof -
        fix m::i
        assume ff: "k \<in> x"
        and gg: "k \<subseteq> x"
        and hh: \<open>m \<in> succ(k)\<close>
        show ii:"m \<in> x"
        proof -
          from hh
          have hh: "m \<in> cons(k, k)"
            by (unfold succ_def)
          from hh
          have hh: "m \<in> Upair(k,k) \<union> k"
            by (unfold cons_def)
          from hh
          have hh: "m \<in> Upair(k,k) \<or> m \<in> k"
            apply (unfold Un_def)
            sorry
          from ff and gg and hh show "m \<in> x"
            sorry
        qed
      qed
      from ik
      show "succ(k) \<in> {y \<in> x . y \<subseteq> x}"
        apply(unfold succ_def)
        apply(fold succ_def)
        apply (rule ik)
        done
    qed
  qed
  show "Ind({y \<in> x . y \<subseteq> x})"
    apply(unfold Ind_def)
    apply(rule conjI)
     apply(rule d)
    apply(rule e)
    done
qed

end
