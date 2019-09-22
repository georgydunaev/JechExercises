theory classical_axioms imports FOL
begin

lemma ax1:\<open>A\<longrightarrow>(B\<longrightarrow>A)\<close>
  apply (rule impI)
  apply (rule impI)
  apply assumption
  done

lemma ax2:\<open>(A\<longrightarrow>(B\<longrightarrow>C))\<longrightarrow>((A\<longrightarrow>B)\<longrightarrow>(A\<longrightarrow>C))\<close>
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (rule mp)
  apply (rule mp)
    apply assumption
 apply assumption
  apply (rule mp)
   apply assumption
 apply assumption
 done

lemma ax3:\<open>(A\<and>B)\<longrightarrow>A\<close>
  apply (rule impI)
  apply (rule conjE)
   apply assumption
  apply assumption
  done

lemma ax4:\<open>(A\<and>B)\<longrightarrow>B\<close>
  apply (rule impI)
  apply (rule conjE)
   apply assumption
  apply assumption
  done

lemma ax5:\<open>A\<longrightarrow>(B\<longrightarrow>(A\<and>B))\<close>
  apply (rule impI)
  apply (rule impI)
  apply (rule conjI)
   apply assumption
   apply assumption
  done

lemma ax6:\<open>A\<longrightarrow>(A\<or>B)\<close>
  apply (rule impI)
  apply (rule disjI1)
  apply assumption
  done

lemma ax7:\<open>B\<longrightarrow>(A\<or>B)\<close>
  apply (rule impI)
  apply (rule disjI2)
  apply assumption
  done

lemma ax8:\<open>(A\<longrightarrow>C)\<longrightarrow>(B\<longrightarrow>C)\<longrightarrow>(A\<or>B\<longrightarrow>C)\<close>
proof
  assume q:"(A\<longrightarrow>C)"
  show "(B \<longrightarrow> C) \<longrightarrow> A \<or> B \<longrightarrow> C"
  proof
    assume q2: "B \<longrightarrow> C"
    show "A \<or> B \<longrightarrow> C"
    apply (rule impI)
    apply (erule disjE)
    apply (rule mp ) (*[THEN swap]*)
    apply (rule q)
    apply assumption
    apply (rule mp )
    apply (rule q2)
    apply assumption
    done
  qed
qed

lemma ax9: "(A\<longrightarrow>B)\<longrightarrow>(A\<longrightarrow>~B)\<longrightarrow>~A"
apply (rule impI)
  apply (rule impI)
(*  apply (unfold not_def) *)
  apply (rule notI)
  apply (rule notE)
  apply (rule mp)
   apply assumption
   apply assumption
  apply (rule mp)
   apply assumption
   apply assumption
  done

lemma ax10: "A\<longrightarrow>~A\<longrightarrow>B"
apply (rule impI)
  apply (rule impI)
  apply (rule notE)
   apply assumption
  apply assumption
  done

lemma ax11: "A\<or>~A"
  apply (rule disjCI)
  apply (rule notnotD)
  apply assumption
  done

lemma ax12: \<open>(\<forall>x. A(x)) \<longrightarrow> A(q)\<close>
proof
  assume r: "\<forall>x. A(x)"
  show "A(q)"
    apply(rule_tac x="q" in allE)
    apply(rule r)
    apply assumption
    done
qed

lemma ax13: \<open>A(q) \<longrightarrow> (\<exists>x. A(x))\<close>
  apply(rule impI)
  apply(rule_tac x="q" in exI)
  apply assumption
  done

lemma B1: \<open>(\<forall>x. (A\<longrightarrow>B(x)))\<Longrightarrow>(A\<longrightarrow>(\<forall>x. B(x)))\<close>
  apply(rule impI)
  apply(rule allI)
  apply (rule mp)
  apply(rule allE)
  apply assumption
  apply assumption
  apply assumption
  done

lemma axB1: \<open>(\<forall>x. (A\<longrightarrow>B(x)))\<longrightarrow>(A\<longrightarrow>(\<forall>x. B(x)))\<close>
  apply(rule impI)
  apply(rule B1)
  apply assumption
  done

lemma B2: \<open>(\<forall>x. (B(x)\<longrightarrow>A))\<Longrightarrow>((\<exists>x. B(x))\<longrightarrow>A)\<close>
  apply(rule impI)
  apply(rule exE)
  apply assumption
  apply (rule mp)
  apply(rule allE)
  apply assumption
  apply assumption
  apply assumption
  done

lemma axB2: \<open>(\<forall>x. (B(x)\<longrightarrow>A))\<longrightarrow>((\<exists>x. B(x))\<longrightarrow>A)\<close>
  apply(rule impI)
  apply(rule B2)
  apply assumption
  done

lemma rB1: \<open>(\<And>z. (R \<longrightarrow> S(z))) \<Longrightarrow> (R \<longrightarrow> (\<forall>x. S(x)))\<close>
  (*apply auto*)
  apply(rule impI)
  apply(rule allI)
  apply(rule mp)
   apply assumption
   apply assumption
  done

lemma rB2: \<open>(\<And>x. (S(x) \<longrightarrow> R)) \<Longrightarrow> ((\<exists>x. S(x)) \<longrightarrow> R)\<close>
  (*apply auto*)
  apply(rule impI)
  apply(rule exE)
   apply assumption
  apply(rule mp)
  apply assumption
  apply assumption
  done

end