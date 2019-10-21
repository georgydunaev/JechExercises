theory different imports set_theory
begin
lemma inSucc' :
  assumes hh: \<open>m \<in> succ(k)\<close>
  shows \<open>m \<in> Upair(k,k) \<or> m \<in> k\<close>
proof -
  from hh
  have "m \<in> cons(k, k)" by (unfold succ_def)
  hence "m \<in> Upair(k,k) \<union> k" by (unfold cons_def)
  thus hh: "m \<in> Upair(k,k) \<or> m \<in> k"
    apply (unfold Un_def)
    apply (erule UnionE)
    apply (erule UpairE)
     apply(rule disjI1)
     apply(erule subst)
     apply assumption
    apply(rule disjI2)
    apply(erule subst)
    apply assumption
    done
qed

lemma Nat0 : "Nat(0)"
  apply(unfold Nat_def)
  apply(unfold ClassInter_def)
  apply(rule allI)
  apply(rule impI)
  apply(unfold Ind_def)
  apply(erule conjE)
  apply assumption
  done

lemma Nat0' : "Nat(0)"
proof (unfold Nat_def) show \<open>ClassInter(Ind, 0)\<close>
  proof (unfold ClassInter_def) show \<open>\<forall>y. Ind(y) \<longrightarrow> 0 \<in> y\<close>
    proof (rule allI) show \<open>\<And>y. Ind(y) \<longrightarrow> 0 \<in> y\<close>
      proof (rule impI) show \<open>\<And>y. Ind(y) \<Longrightarrow> 0 \<in> y\<close>
        proof (unfold Ind_def) show \<open>\<And>y. 0 \<in> y \<and> (\<forall>ya\<in>y. succ(ya) \<in> y) \<Longrightarrow> 0 \<in> y\<close>
          proof (erule conjE) show
                 \<open>\<And>y. 0 \<in> y \<Longrightarrow>
                  \<forall>ya\<in>y. succ(ya) \<in> y \<Longrightarrow>
                  0 \<in> y\<close>
              by assumption
          qed
        qed
      qed
    qed
  qed
qed

lemma wrongNatInInf: "\<And>x. x \<in> Inf \<Longrightarrow> Nat(x)"
  apply (unfold Nat_def)
  apply (unfold ClassInter_def)
  apply(rule allI)
  apply(rule impI)
  oops (* lemma is false *)

lemma zeroisempty : \<open>\<forall>x. \<not> x \<in> 0\<close>
  apply(rule allI)
  apply(rule not_mem_empty)
  done


(* "is a superset of the natural numbers" predicate *)
definition SuperNatNumb :: \<open>(i\<Rightarrow>o)\<close>
  where SuperNatNumb_def : "SuperNatNumb(x) == \<forall> y. Nat(y) \<longrightarrow> y\<in>x"

lemma SuperNatNumbInf : "SuperNatNumb(Inf)"
  apply (unfold SuperNatNumb_def)
  apply(rule allI)
  apply(rule impI)
  apply(erule NatInInf)
  done

lemma NatI : "\<And>x. Nat(x) \<Longrightarrow> x\<in>The(SuperNatNumb)"
  apply (unfold the_def)
  apply(rule UnionI)
   apply(rule ReplaceI)
  prefer 4
(*     apply(erule NatInInf) wrong!
    apply(rule SuperNatNumbInf)
     apply assumption *)
  oops


lemma ww1:\<open>k \<in> x \<Longrightarrow> m \<in> Upair(k, k) \<Longrightarrow> m \<in> x\<close>
proof (erule UpairE)
  show \<open>k \<in> x \<Longrightarrow> m = k \<Longrightarrow> m \<in> x\<close> by (erule subst_elem)
next
  show \<open>k \<in> x \<Longrightarrow> m = k \<Longrightarrow> m \<in> x\<close> by (erule subst_elem)
qed

lemma l3': \<open>S \<subseteq> {b . a \<in> S, a = b}\<close>
proof (rule subsetI)
  fix x
  assume p2:\<open>x \<in> S\<close>
  have p1:"x=x" by (rule refl)
  have p3:"\<And>b. x=b \<Longrightarrow> b=x" by (rule sym)
  from p1 and p2 and p3 show \<open>x \<in> {b . a \<in> S, a = b}\<close> by (rule ReplaceI)
qed

(* original theorem has no name, so I had to prove it... *)
lemma l4_1:  \<open>P \<longleftrightarrow> P \<and> True\<close>
  apply auto
  done


lemma l4: \<open>S = {a \<in> S. True}\<close>
  (* apply(rule iffD2)
  apply(rule extension)
  apply(rule conjI) *)
  apply(rule equalityI)
  apply(unfold Collect_def)
   apply(rule subst)
(*proof -
  let ?a3 = S*)

    apply(rule Replace_cong)
     apply(rule refl)
(* how to forget assumption? *)
    apply(rule l4_1)
  apply(rule l3)
  apply(fold Collect_def)
  apply(rule Collect_subset)
  done


lemma lwe4' : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
proof 
  fix x
  show \<open>(Nat(x) \<longrightarrow> x\<in>Inf)\<close>
  proof
    assume \<open>Nat(x)\<close>
    hence \<open>ClassInter(Ind, x)\<close> by (unfold Nat_def)
    hence \<open>\<forall>y. Ind(y) \<longrightarrow> x \<in> y\<close> by (unfold ClassInter_def)
    hence \<open>Ind(Inf) \<longrightarrow> x \<in> Inf\<close> by (rule spec)
    hence p:\<open>Ind(Inf) \<Longrightarrow> x \<in> Inf\<close> by (rule mp)
    from IndInf show \<open>x \<in> Inf\<close> by (rule p)
  qed
qed


lemma lwe2 : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
  apply(unfold Nat_def)
  apply(rule allI)
  apply(rule impI)
  apply(unfold ClassInter_def)
  apply(rule mp)
   apply(erule spec)
  apply(rule IndInf)
  done

(*lemma IndPO*)

lemma ExMinInd : \<open>\<exists>!x. ( Ind(x) \<and> (\<forall>y. Ind(y) \<longrightarrow> x\<subseteq>y) )\<close>
  apply(rule ex_ex1I)
   apply(rule exI)
   apply(rule conjI)
    apply(rule IndOmega)
  sorry

(*If there exists two subset-minimal sets  the they are equal.*)



lemma l3: \<open>S \<subseteq> {b . a \<in> S, a = b}\<close>
  apply(rule subsetI)
  apply(rule ReplaceI)
  (*apply(rule iffD2)
  (* apply(unfold Replace_def)
   apply(rule replacement) *)
   apply(rule Replace_iff)*
  apply(unfold Bex_def)
  (* How to specify metavariable with bounded variable? "let ?x = "
     apply(rule exI[where x=x])  [of _ x]*)
  apply(rule exI)
  apply(erule conjI)
  (* How to instantiate ?x8(x):=x  ? *)
  apply(rule conjI) (* = split.*)*)
    apply(rule refl)
   apply assumption
  apply(erule sym)
  done


lemma IndInf_' : "Ind(Inf)"
  apply(unfold Ind_def, rule infinity)
  done

end