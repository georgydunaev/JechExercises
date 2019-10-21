theory set_theory imports trivia classical_axioms fol_theorems
begin

(* ex 1.1: Verify (a, b) = (c, d) if and only if a = c and b = d. *)
theorem ex_1_1 : \<open><a,b> = <c,d> \<longleftrightarrow> a=c & b=d\<close>
  by (rule pair.Pair_iff)

(* ex 1.2: There is no set X such that Pow(X)\<subseteq>X. *)
context
  fixes S
  fixes W defines W_def : \<open>W == {x\<in>S. x\<notin>x}\<close>
begin

lemma WinW :
  assumes y : \<open>W \<in> W\<close> 
  shows \<open>False\<close>
proof (rule notE[where P="W\<in>W"])
  from y have \<open>W \<in> {x \<in> S . x \<notin> x}\<close> by (unfold W_def)
  then show \<open>W \<notin> W\<close> by (rule CollectD2)
next
  show \<open>W \<in> W\<close> by (rule y)
qed

theorem ex_1_2 : \<open>\<not> ( Pow(S) \<subseteq> S )\<close>
proof (rule notI)
  assume \<open>Pow(S) \<subseteq> S\<close>
  have \<open>{x \<in> S . x \<notin> x} \<subseteq> S\<close> using CollectD1 by (rule subsetI)
  hence \<open>W \<subseteq> S\<close> by (unfold W_def)
  hence \<open>W \<in> Pow(S)\<close> by (rule PowI)
  with \<open>Pow(S) \<subseteq> S\<close> have \<open>W \<in> S\<close> by (rule subsetD)
  show \<open>False\<close>
  proof (rule case_split[where P="W\<in>W"])
    show \<open>W \<in> W \<Longrightarrow> False\<close> by (rule WinW)
  next
    from \<open>W \<in> S\<close> have \<open>{x \<in> S . x \<notin> x} \<in> S\<close> by (unfold W_def) moreover
    assume \<open>W \<notin> W\<close>
    hence \<open>{x \<in> S . x \<notin> x} \<notin> {x \<in> S . x \<notin> x}\<close> by (unfold W_def)
    ultimately have \<open>{x \<in> S . x \<notin> x} \<in> {x \<in> S . x \<notin> x}\<close> by (rule CollectI)
    hence \<open>W \<in> W\<close> by (fold W_def) 
    with \<open>W \<notin> W\<close>
    show \<open>False\<close> by (rule notE)
  qed
qed
end

(* ex 1.3: If X is inductive, then the set {x \<in> X : x \<subseteq> X} is inductive. Hence N is
transitive, and for each n, n = {m \<in> N : m < n}. *)
definition Ind :: "i\<Rightarrow>o"
  where Ind_def : "Ind(x) == 0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)"

lemma IndInf : \<open>Ind(Inf)\<close>
  by(unfold Ind_def, rule infinity)

lemma IndE2 :
  assumes a:\<open>Ind(x)\<close>
  shows \<open>\<And>xa. xa \<in> x \<Longrightarrow> succ(xa) \<in> x\<close>
proof -
  from a
  have \<open>0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close> by (unfold Ind_def)
  hence \<open>(\<forall>y\<in>x. succ(y) \<in> x)\<close> by (rule conjunct2)
  hence \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close> by (unfold Ball_def)
  thus \<open>\<And>xa. xa \<in> x \<Longrightarrow> succ(xa) \<in> x\<close> by (rule spec[THEN impE])
qed

context
  fixes x
  assumes a:\<open>Ind(x)\<close>
begin
lemma lem0 : \<open>\<And>xa. xa \<in> {y \<in> x . y \<subseteq> x} \<Longrightarrow>
          succ(xa) \<in> {y \<in> x . y \<subseteq> x}\<close> 
proof -
  fix k
  assume h:\<open>k \<in> {y \<in> x . y \<subseteq> x}\<close>
  from h have h1:\<open>k \<in> x\<close> by (rule CollectD1[where A="x"])
  from h have h2:\<open>k \<subseteq> x\<close> by (rule CollectD2[where P="\<lambda>w. w\<subseteq>x"])
  from a and h1 have \<open>succ(k) \<in> x\<close> by (rule IndE2)
  (*\<open>k \<subseteq> x\<close>*)
  have \<open>\<And>xa. xa \<in> succ(k) \<Longrightarrow> xa \<in> x\<close>
  proof -
    fix xa
    assume \<open>xa \<in> succ(k)\<close>
    then have \<open>xa = k \<or> xa \<in> k\<close> by (rule inSucc)
    then show \<open>xa \<in> x\<close>
    proof (rule disjE)
      assume \<open>xa = k\<close>
      with h1 show \<open>xa \<in> x\<close> by (rule subst_elem)
    next
      assume \<open>xa \<in> k\<close>
      with h2  show \<open>xa \<in> x\<close> by (rule subsetD)
    qed
  qed
  hence \<open>succ(k) \<subseteq> x\<close> by (rule subsetI)
  with \<open>succ(k) \<in> x\<close>
  show \<open>succ(k) \<in> {y \<in> x . y \<subseteq> x}\<close> by (rule CollectI[where P="\<lambda>y. y\<subseteq>x"])
qed  

theorem ex1_3:
  shows \<open>Ind({y\<in>x. y\<subseteq>x})\<close>
proof -
  from a
  have \<open>0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close> by (unfold Ind_def)
  hence \<open>0 \<in> x\<close> by (rule conjunct1)
  have \<open>0 \<subseteq> x\<close> by (rule empty_subsetI)
  with \<open>0 \<in> x\<close> have d:"0 \<in> {y \<in> x . y \<subseteq> x}" by (rule CollectI)

  from lem0 have \<open>\<And>xa. xa \<in> {y \<in> x . y \<subseteq> x} \<longrightarrow> succ(xa) \<in> {y \<in> x . y \<subseteq> x}\<close>
    by (rule impI)
  hence \<open>\<forall>xa. xa \<in> {y \<in> x . y \<subseteq> x} \<longrightarrow> succ(xa) \<in> {y \<in> x . y \<subseteq> x}\<close>
    by (rule allI)
  hence \<open>(\<forall>y\<in>{y \<in> x . y \<subseteq> x}. succ(y) \<in> {y \<in> x . y \<subseteq> x})\<close>
    by (fold Ball_def)
  with d have \<open>0 \<in> {y \<in> x . y \<subseteq> x} \<and> (\<forall>y\<in>{y \<in> x . y \<subseteq> x}. succ(y) \<in> {y \<in> x . y \<subseteq> x})\<close>
    by (rule conjI)
  thus "Ind({y \<in> x . y \<subseteq> x})" by (fold Ind_def)
qed

end

definition ClassInter :: \<open>(i\<Rightarrow>o)\<Rightarrow>(i\<Rightarrow>o)\<close> (*\<open>[ i \<Rightarrow> o, i ] \<Rightarrow> o\<close>*)
  where ClassInter_def : "ClassInter(P,x) == \<forall>y. P(y) \<longrightarrow> x\<in>y"

definition Nat :: \<open>i\<Rightarrow>o\<close>
  where "Nat == ClassInter(Ind)"

lemma NatSubInf : \<open>\<And>x. Nat(x) \<Longrightarrow> x\<in>Inf\<close>
proof (unfold Nat_def)
  fix x
  assume p0:\<open>ClassInter(Ind, x)\<close>
  show \<open>x\<in>Inf\<close>
  proof -
    from p0 have "\<forall>y. Ind(y) \<longrightarrow> x \<in> y" by (unfold ClassInter_def)
    then have "Ind(Inf) \<longrightarrow> x \<in> Inf" by (rule spec)
    then have p3:"Ind(Inf) \<Longrightarrow> x \<in> Inf" by (rule mp)
    from IndInf show p4:"x \<in> Inf" by (rule p3)
  qed
qed

lemma NatSubInf' : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
proof (rule allI)
  fix x from NatSubInf show \<open>(Nat(x) \<longrightarrow> x\<in>Inf)\<close> by (rule impI)
qed

definition IsTransClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsTransClass_def : "IsTransClass(P) == \<forall>y. P(y) \<longrightarrow> (\<forall>z. z\<in>y \<longrightarrow> P(z))"

lemma Nat0 : \<open>Nat(0)\<close>
proof -
  have \<open>\<And>y. 0 \<in> y \<and> (\<forall>ya\<in>y. succ(ya) \<in> y) \<Longrightarrow> 0 \<in> y\<close> by (erule conjE)
  hence  \<open>\<And>y. Ind(y) \<Longrightarrow> 0 \<in> y\<close> by (unfold Ind_def)
  hence \<open>\<And>y. Ind(y) \<longrightarrow> 0 \<in> y\<close> by (rule impI)
  hence \<open>\<forall>y. Ind(y) \<longrightarrow> 0 \<in> y\<close> by (rule allI)
  hence \<open>ClassInter(Ind, 0)\<close> by (unfold ClassInter_def) 
  thus ?thesis by (unfold Nat_def)
qed

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

definition IsIndClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsIndClass_def : \<open>IsIndClass(P) == P(0) \<and> (\<forall>y. P(y) \<longrightarrow> P(succ(y)))\<close>

lemma NatIsInd : \<open>IsIndClass(Nat)\<close>
  apply (unfold IsIndClass_def)
  apply (rule conjI)
   apply (rule Nat0)
  apply (rule NatSucc)
  done

definition Omega :: \<open>i\<close>
  where Omega_def : "Omega == { y \<in> Inf . Nat(y) }"

lemma NatSubOmega : "\<And>x. Nat(x) \<Longrightarrow> x \<in> Omega"
  apply (unfold Omega_def)
  apply (rule CollectI)
   apply (erule NatSubInf)
  apply assumption
  done

end
