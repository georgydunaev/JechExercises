theory set_theory_comments imports ZFC classical_axioms fol_theorems
begin

lemma l5':
(*  define x where x \<equiv> 0*)
 \<open>\<exists>x. x=x\<close>
  apply(rule exI)
  apply(rule refl)
  done

lemma l5': \<open>\<exists>x. x=x\<close>
proof -
  obtain y::i where "y = y"
    by (auto)
  then show ?thesis
  (*proof -*)
    apply (rule exI[of "y=y"])
  qed
[where P="y=y"])

      by(rule exI[of "y=y" "y"])

lemma "\<exists> x. x * (t :: nat) = t"
proof - (* method - does not change the goal *)
  obtain y where "y * t = t" by (auto)
  then show ?thesis by(rule exI)
qed

(* “by method1 method2” for “proof method1 qed method2” 
from a\<equiv>note a then 
with a \<equiv> from a and this \<equiv> note a and this then*)
print_statement exE
print_statement conjE
print_statement disjE
(* good
lemma ex1_3 : "Ind(x) \<Longrightarrow> Ind({y\<in>x. y\<subseteq>x})"
proof -
  assume q:"Ind(x)" show b:"Ind({y\<in>x. y\<subseteq>x})"
  proof -
    from q have b: "0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)" 
      by (unfold Ind_def)
    from b have c1:"0 \<in> x" and c2:"(\<forall>y\<in>x. succ(y) \<in> x)"
      by (rule conjunct1, rule conjunct2)
    show "Ind({y \<in> x . y \<subseteq> x})"
      apply(unfold Ind_def)
      apply(rule conjI)
       apply(rule CollectI)
        apply(rule c1)
       apply(rule empty_subsetI)

  apply(unfold Ball_def, rule allI, rule impI)
    proof -
      fix xa
      assume d:"xa \<in> {y \<in> x . y \<subseteq> x}" show e:"succ(xa) \<in> {y \<in> x . y \<subseteq> x}"
      proof -
        oops
*)
lemma l0:"True"
  apply(rule TrueI)
  done

lemma l2: \<open>(\<lambda>a b. True)(x,z)\<close>
  apply(rule TrueI)
  done

(* subsetI
  apply(unfold subset_def)
  apply(unfold Ball_def)
  apply(rule allI) (* intro *) 
  apply(rule impI) (* intro *)
*)
lemma collect_is_subset: \<open>{a \<in> S . A} \<subseteq> S\<close>
  apply(rule subsetI)
  apply(rule CollectD1)
  apply assumption
  done

lemma example1 : "\<And>x. x=x"
  apply(rule refl)
  done

lemma example2 : "x=x"
  apply(rule example1) done

lemma l5: \<open>\<exists>x. x=x\<close>
  apply(rule exI)
  apply(rule refl)
  done
(* CollectD1
  apply(rule conj_simps)
\<open>P \<and> True \<longleftrightarrow> P\<close>)
 \<open>P \<and> True \<longleftrightarrow> P\<close>
 True
  apply(rule RepFun_cong)
  apply(rule Collect_cong) *)

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

end

(*
lemma lemm:"\<lbrakk>A\<Longrightarrow>A,B\<Longrightarrow>B\<rbrakk>" gives error
therefore \<lbrakk>A,B\<rbrakk>\<Longrightarrow>C is nothing but syntactic sugar for A\<Longrightarrow>(B\<Longrightarrow>C)
*)
(*
lemma Collect_cong [cong]:
    "[| A=B;  \<And>x. x\<in>B \<Longrightarrow> P(x) <-> Q(x) |]
*)


(*lemma yuyu:" 0 \<subseteq> x"*)
-----------
(*
show "(\<forall>y\<in>{y \<in> x . y \<subseteq> x}. succ(y) \<in> {y \<in> x . y \<subseteq> x})"

"succ(k) \<in> {y \<in> x . y \<subseteq> x}"
      done
      from ik show "succ(k) \<in> {y \<in> x . y \<subseteq> x}"

 apply(rule assms)

      show "succ(k) \<in> {y \<in> x . y \<subseteq> x}"
      prefer 1
      print_statement conjE

  obtain ik
     
    qed
      


(*         prefer 2
         apply(unfold cons_def)*)

        (*apply(rule CollectI[where a="succ(k)" [where P="\<lambda>y. y\<subseteq>x"]])*)
        (*apply(rule h1)*)
      qed

show i:"succ(k) \<in> {y \<in> x . y \<subseteq> x}"
    show i (*:"succ(k) \<in> {y \<in> x . y \<subseteq> x}"*)


       apply(rule mp, rule spec)
      prefer 2 apply()


    from f: "0 \<in> x"
     and g:\<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
    have h:\<open>succ(xa) \<in> {y \<in> x . y \<subseteq> x}\<close>
   
    apply(unfold Ball_def, rule allI, rule impI)

qed*)
(* 0 \<in> {y \<in> x . y \<subseteq> x} \<and> (\<forall>y\<in>{y \<in> x . y \<subseteq> x}. succ(y) \<in> {y \<in> x . y \<subseteq> x}) *)


   (*   by (unfold Ind_def) *)
(*      by(unfold Ind_def)

*)
(*  assume q:"Ind(x)"
  have "Ind({y\<in>x. y\<subseteq>x})"
    apply(unfold Ind_def)
    apply(rule conjI)
    proof
      have "0 \<in> {y \<in> x . y \<subseteq> x}"
        apply(rule CollectI)
        proof -
        (*assume q:"Ind(x)"*)
          from q have "0 \<in> x"
            apply(unfold Ind_def)       
            apply (rule assms)
            apply assumption

            apply(rule q)*)
  oops