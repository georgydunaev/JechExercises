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
     apply (erule spec[where x=W])
    apply (rule PowI)
    apply (unfold W_def)
    apply (unfold subset_def)
    apply (unfold Ball_def)
    apply (rule allI)
    apply (rule impI)
    apply (erule CollectD1)
  done
end 

lemma l3: \<open>S \<subseteq> {b . a \<in> S, a = b}\<close>
  apply(rule subsetI)
  apply(rule ReplaceI)
  (*apply(rule iffD2)
  (* apply(unfold Replace_def)
   apply(rule replacement) *)
   apply(rule Replace_iff)*
  apply(unfold Bex_def)
  (* How to specify metavariable with bounded variable?
     apply(rule exI[where x=x])  [of _ x]*)
  apply(rule exI)
  apply(erule conjI)
  (* How to instantiate ?x8(x):=x  ? *)
  apply(rule conjI) (* = split.*)*)
    apply(rule refl)
   apply assumption
  apply(erule sym)
  done

(* original theorem has no name, so... *)
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

lemma Ind_Inf : "Ind(Inf)"
  apply(unfold Ind_def, rule infinity)
  done

lemma ex1_3:
  fixes x
  assumes a:"Ind(x)"
  shows "Ind({y\<in>x. y\<subseteq>x})"
proof -
  from a
  have b: "0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)"
  proof (unfold Ind_def) qed
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
            apply (erule UnionE)
            apply (erule UpairE)
             apply(rule disjI1)
             apply(erule subst)
             apply assumption
             apply(rule disjI2)
             apply(erule subst)
            apply assumption
            done
          from ff and gg and hh show "m \<in> x"
          proof -
            show ghj:"k \<in> x \<Longrightarrow> k \<subseteq> x \<Longrightarrow> m \<in> Upair(k, k) \<or> m \<in> k \<Longrightarrow> m \<in> x"
              apply(erule disjE)
               apply (erule UpairE)
                (*apply(rule subst[where P = "\<lambda>m. m\<in>x"])
                 apply(rule sym)*)
              apply(erule subst_elem)
                 apply assumption
               apply(erule subst_elem)
                apply assumption
(* subst_elem *)
              apply(erule subsetD)
              apply assumption
              done
          qed
        qed
      qed
      from ik
      show "succ(k) \<in> {y \<in> x . y \<subseteq> x}"
        apply(unfold succ_def)
        apply(fold succ_def)
        apply(rule ik)
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

definition ClassInter :: \<open>(i\<Rightarrow>o)\<Rightarrow>(i\<Rightarrow>o)\<close> (*\<open>[ i \<Rightarrow> o, i ] \<Rightarrow> o\<close>*)
  where ClassInter_def : "ClassInter(P,x) == \<forall>y. P(y) \<longrightarrow> x\<in>y"

definition Nat :: \<open>i\<Rightarrow>o\<close>
  where "Nat == ClassInter(Ind)"

(*lemma Ind_Inf : "Ind(Inf)"
  apply(unfold Ind_def, rule infinity)
  done*)

lemma lwe : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
  apply(unfold Nat_def)
  apply(rule allI)
  apply(rule impI)
  apply(unfold ClassInter_def)
  apply(rule mp)
   apply(erule spec)
  apply(rule Ind_Inf)
  done

(*lemma : "Nat"*)


definition IsTransClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsTransClass_def : "IsTransClass(P) == \<forall>y. P(y) \<longrightarrow> (\<forall>z. z\<in>y \<longrightarrow> P(z))"

definition IsIndClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsIndClass_def : "IsIndClass(P) == P(0) \<and> (\<forall>y. P(y) \<longrightarrow> P(succ(y)))"

definition IsSet :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsSet_def : "IsSet(P) == \<exists> y. \<forall> z. z \<in> y \<longleftrightarrow> P(z)"

lemma Nat0 : "Nat(0)"
  apply (unfold Nat_def)
  apply (unfold ClassInter_def)
  apply(rule allI)
  apply(rule impI)
  apply (unfold Ind_def)
  apply(rule conjE)
   apply assumption
  apply assumption
  done

lemma NatSu:
  fixes x w
  assumes a:"\<forall>y. Ind(y) \<longrightarrow> x \<in> y"
  assumes b:"Ind(w)"
  shows "succ(x) \<in> w"
proof -
  from b
  have b': "\<forall>y. y\<in>w \<longrightarrow> succ(y) \<in> w"
    apply(unfold Ind_def)
    apply(rule allI)
    apply(rule impI)
    apply(rule  bspec[where P="%y. succ(y) \<in> w"])
     apply(erule conjunct2)
    apply(assumption)
    done
  from a b' b
  show c': "succ(x) \<in> w"
    apply(unfold Ind_def)
    apply(rule mp)
     apply(erule spec)
    apply(fold Ind_def)
    apply(rule mp)
     apply(erule spec)
    apply(unfold Ind_def)

    apply(rule conjI)
    prefer 2
     apply(rule ballI)
     apply(rule mp)
      apply(erule spec)
     apply(assumption)
    apply(erule conjunct1)
    done
qed

lemma NatSucc : "\<forall> x. Nat(x) \<longrightarrow> Nat(succ(x))"
  apply (unfold Nat_def)
  apply (unfold ClassInter_def)
  apply(rule allI)
  apply(rule impI)
  apply(rule allI)
  apply(rule impI)
  apply(erule NatSu)
  apply assumption
  done

lemma NatIsInd : \<open>IsIndClass(Nat)\<close>
  apply (unfold IsIndClass_def)
  apply (rule conjI)
   apply (rule Nat0)
  apply (rule NatSucc)
  done

lemma uio : \<open>IsTransClass(Nat)\<close>
  apply (unfold IsTransClass_def)
  apply(rule allI)
  apply(rule impI)
  apply(rule allI)
  apply(rule impI)
  apply (unfold Nat_def)
  apply (unfold ClassInter_def)
  apply(rule allI)
  apply(rule impI)
  apply (unfold Ind_def)
  oops

lemma TheE : "\<And>x. P(x) \<Longrightarrow> x\<in>The(P)"
  apply (unfold the_def)
  apply(rule UnionI)
   apply(rule ReplaceI)
     apply assumption
  oops

definition NatNumb :: \<open>(i\<Rightarrow>o)\<close>
  where NatNumb_def : "NatNumb(x) == \<forall> y. Nat(y) \<longleftrightarrow> y\<in>x"

lemma NatInInf: "\<And>x. Nat(x) \<Longrightarrow> x \<in> Inf"
  apply (unfold Nat_def)
  apply (unfold ClassInter_def)
  apply(rule mp)
   apply(erule spec)
  apply (rule Ind_Inf)
  done

lemma NatI : "\<And>x. Nat(x) \<Longrightarrow> x\<in>The(NatNumb)"
  apply (unfold the_def)
  apply(rule UnionI)
   apply(rule ReplaceI)
     prefer 4
     apply(erule NatInInf)

     apply assumption
  oops


lemma NatIsInd2: "Ind(The(Nat))"
  oops

end
