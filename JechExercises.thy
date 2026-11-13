(*  Title:       Jech Exercises
    Author:      Georgy Dunaev <georgedunaev at gmail.com>, 2019
    Maintainer:  Georgy Dunaev <georgedunaev at gmail.com>
*)

section "Jech Exercises"
theory JechExercises imports trivia filters
begin

text \<open>preliminaries\<close>
definition Ind :: \<open>i\<Rightarrow>o\<close>
  where Ind_def : \<open>Ind(x) == 0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close>

lemma IndInf : \<open>Ind(Inf)\<close>
  by(unfold Ind_def, rule infinity)

lemma IndI :
  assumes c0 : \<open>0 \<in> x\<close>
      and cS : \<open>\<And>xa. xa \<in> x \<Longrightarrow> succ(xa) \<in> x\<close>
    shows \<open>Ind(x)\<close>
proof -
  from cS have \<open>\<And>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
    by (rule impI)
  hence \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
    by (rule allI)
  hence \<open>(\<forall>y\<in>x. succ(y) \<in> x)\<close>
    by (fold Ball_def)
  with c0 have \<open>0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close>
    by (rule conjI)
  thus \<open>Ind(x)\<close> by (fold Ind_def)
qed

lemma IndE1 :
  assumes a:\<open>Ind(x)\<close>
  shows \<open>0 \<in> x\<close>
proof -
  from a
  have \<open>0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close> by (unfold Ind_def)
  thus \<open>0 \<in> x\<close> by (rule conjunct1)
qed

lemma IndE2 :
  assumes a:\<open>Ind(x)\<close>
  shows \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close>
proof -
  from a
  have \<open>0 \<in> x \<and> (\<forall>y\<in>x. succ(y) \<in> x)\<close> by (unfold Ind_def)
  hence \<open>(\<forall>y\<in>x. succ(y) \<in> x)\<close> by (rule conjunct2)
  thus \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close> by (unfold Ball_def)
qed

lemma IndE2R :
  assumes \<open>Ind(x)\<close>
  shows \<open>\<And>xa. xa \<in> x \<Longrightarrow> succ(xa) \<in> x\<close>
proof -
  from \<open>Ind(x)\<close> have \<open>\<forall>xa. xa \<in> x \<longrightarrow> succ(xa) \<in> x\<close> by (rule IndE2)
  thus \<open>\<And>xa. xa \<in> x \<Longrightarrow> succ(xa) \<in> x\<close> by (rule spec[THEN impE])
qed

text \<open>ex 1.1: Verify (a, b) = (c, d) if and only if a = c and b = d.\<close>

theorem ex_1_1 : \<open><a,b> = <c,d> \<longleftrightarrow> a=c & b=d\<close>
  by (rule pair.Pair_iff)

lemma Pair_fst : \<open>fst(<a,b>) = a\<close>
  by (rule fst_conv)

lemma Pair_snd : \<open>snd(<a,b>) = b\<close>
  by (rule snd_conv)

lemma prod_Un_distrib1 : \<open>(A \<union> B) \<times> C = (A \<times> C) \<union> (B \<times> C)\<close>
  by blast

lemma prod_Int_distrib1 : \<open>(A \<inter> B) \<times> C = (A \<times> C) \<inter> (B \<times> C)\<close>
  by blast

lemma prod_Diff_distrib1 : \<open>(A - B) \<times> C = (A \<times> C) - (B \<times> C)\<close>
  by blast

lemma prod_Un_distrib2 : \<open>A \<times> (B \<union> C) = (A \<times> B) \<union> (A \<times> C)\<close>
  by blast

lemma prod_Int_distrib2 : \<open>A \<times> (B \<inter> C) = (A \<times> B) \<inter> (A \<times> C)\<close>
  by blast

lemma prod_Diff_distrib2 : \<open>A \<times> (B - C) = (A \<times> B) - (A \<times> C)\<close>
  by blast

text \<open>ex 1.2: There is no set X such that $Pow(X)\subseteq X$.\<close>
context
  fixes S
  fixes W defines W_def : \<open>W == {x\<in>S. x\<notin>x}\<close>
begin

lemma notWinW :
  assumes y : \<open>W \<in> W\<close> 
  shows \<open>False\<close>
proof (rule notE[where P=\<open>W \<in> W\<close>])
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
  proof (rule case_split[where P=\<open>W \<in> W\<close>])
    show \<open>W \<in> W \<Longrightarrow> False\<close> by (rule notWinW)
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

theorem no_universal_set : \<open>\<not> (\<exists>V. \<forall>x. x \<in> V)\<close>
proof (rule notI)
  assume \<open>\<exists>V. \<forall>x. x \<in> V\<close>
  then obtain V where hV:\<open>\<forall>x. x \<in> V\<close> by (rule exE)
  have \<open>Pow(V) \<subseteq> V\<close>
  proof (rule subsetI)
    fix y assume \<open>y \<in> Pow(V)\<close>
    from hV show \<open>y \<in> V\<close> by (rule spec)
  qed
  with ex_1_2[where S=V] show False by (rule notE)
qed

text \<open>ex 1.3: If X is inductive, then the set $\{x \in X : x \subseteq X\}$ is inductive. Hence N is
transitive, and for each n, $n = \{m \in N : m < n\}$.\<close>
context
  fixes x
  assumes a:\<open>Ind(x)\<close>
begin
lemma subsetsu : \<open>\<And>xa. xa \<in> {y \<in> x . y \<subseteq> x} \<Longrightarrow>
          succ(xa) \<in> {y \<in> x . y \<subseteq> x}\<close> 
proof -
  fix k
  assume h:\<open>k \<in> {y \<in> x . y \<subseteq> x}\<close>
  from h have h1:\<open>k \<in> x\<close> by (rule CollectD1[where A=\<open>x\<close>])
  from h have h2:\<open>k \<subseteq> x\<close> by (rule CollectD2[where P=\<open>\<lambda>w. w\<subseteq>x\<close>])
  from a and h1 have \<open>succ(k) \<in> x\<close> by (rule IndE2R)
  have \<open>\<And>xa. xa \<in> succ(k) \<Longrightarrow> xa \<in> x\<close>
  proof -
    fix xa
    assume \<open>xa \<in> succ(k)\<close>
    hence \<open>xa = k \<or> xa \<in> k\<close> by (rule SuccE)
    thus \<open>xa \<in> x\<close>
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
  show \<open>succ(k) \<in> {y \<in> x . y \<subseteq> x}\<close> by (rule CollectI[where P=\<open>\<lambda>y. y\<subseteq>x\<close>])
qed  

theorem ex1_3:
  shows \<open>Ind({y\<in>x. y\<subseteq>x})\<close>
proof -
  from a
  have \<open>0 \<in> x\<close> by (rule IndE1)
  have \<open>0 \<subseteq> x\<close> by (rule empty_subsetI)
  with \<open>0 \<in> x\<close> have d:\<open>0 \<in> {y \<in> x . y \<subseteq> x}\<close> by (rule CollectI)
  from d and subsetsu show \<open>Ind({y\<in>x. y\<subseteq>x})\<close> by (rule IndI)
qed

end

text \<open>ex 1.4: If X is inductive, then $\{x \in X : x \text{ is transitive}\}$ is inductive.\<close>

lemma trans_empty: \<open>Transset(0)\<close>
  unfolding Transset_def by auto

lemma trans_succ:
  assumes \<open>Transset(y)\<close>
  shows \<open>Transset(succ(y))\<close>
proof (unfold Transset_def, rule ballI)
  fix z assume \<open>z \<in> succ(y)\<close>
  hence \<open>z = y \<or> z \<in> y\<close> by (rule SuccE)
  thus \<open>z \<subseteq> succ(y)\<close>
  proof (rule disjE)
    assume \<open>z = y\<close>
    have \<open>y \<subseteq> succ(y)\<close> by (unfold succ_def, auto)
    with \<open>z = y\<close> show \<open>z \<subseteq> succ(y)\<close> by (rule subst_elem)
  next
    assume \<open>z \<in> y\<close>
    with assms have \<open>z \<subseteq> y\<close> by (unfold Transset_def, blast)
    moreover have \<open>y \<subseteq> succ(y)\<close> by (unfold succ_def, auto)
    ultimately show \<open>z \<subseteq> succ(y)\<close> by (rule subset_trans)
  qed
qed

theorem ex1_4:
  assumes \<open>Ind(x)\<close>
  shows \<open>Ind({y \<in> x. Transset(y)})\<close>
proof -
  from assms have \<open>0 \<in> x\<close> by (rule IndE1)
  have \<open>Transset(0)\<close> by (rule trans_empty)
  with \<open>0 \<in> x\<close> have d0:\<open>0 \<in> {y \<in> x. Transset(y)}\<close> by (rule CollectI)
  have dS:\<open>\<And>ya. ya \<in> {y \<in> x. Transset(y)} \<Longrightarrow> succ(ya) \<in> {y \<in> x. Transset(y)}\<close>
  proof -
    fix ya
    assume h:\<open>ya \<in> {y \<in> x. Transset(y)}\<close>
    from h have h1:\<open>ya \<in> x\<close> by (rule CollectD1)
    from h have h2:\<open>Transset(ya)\<close> by (rule CollectD2)
    from assms and h1 have s1:\<open>succ(ya) \<in> x\<close> by (rule IndE2R)
    from h2 have s2:\<open>Transset(succ(ya))\<close> by (rule trans_succ)
    from s1 and s2 show \<open>succ(ya) \<in> {y \<in> x. Transset(y)}\<close> by (rule CollectI)
  qed
  from d0 and dS show \<open>Ind({y \<in> x. Transset(y)})\<close> by (rule IndI)
qed

text \<open>ex 1.5: Foundation and Well-Foundedness of Membership\<close>

lemma no_self_membership: \<open>x \<notin> x\<close>
proof (rule notI)
  assume h:\<open>x \<in> x\<close>
  have \<open>{x} \<noteq> 0\<close> by auto
  hence \<open>\<exists>y\<in>{x}. y \<inter> {x} = 0\<close> by (rule foundation)
  then obtain y where y1:\<open>y \<in> {x}\<close> and y2:\<open>y \<inter> {x} = 0\<close> by (rule bexE)
  from y1 have \<open>y = x\<close> by auto
  with y2 have \<open>x \<inter> {x} = 0\<close> by (rule subst)
  moreover from h have \<open>x \<in> x \<inter> {x}\<close> by auto
  ultimately show False by auto
qed

lemma no_two_cycle: \<open>\<not> (x \<in> y \<and> y \<in> x)\<close>
proof (rule notI)
  assume h:\<open>x \<in> y \<and> y \<in> x\<close>
  hence h1:\<open>x \<in> y\<close> and h2:\<open>y \<in> x\<close> by (rule conjunct1, rule conjunct2)
  have \<open>{x, y} \<noteq> 0\<close> by auto
  hence \<open>\<exists>z\<in>{x, y}. z \<inter> {x, y} = 0\<close> by (rule foundation)
  then obtain z where z1:\<open>z \<in> {x, y}\<close> and z2:\<open>z \<inter> {x, y} = 0\<close> by (rule bexE)
  from z1 have \<open>z = x \<or> z = y\<close> by auto
  thus False
  proof (rule disjE)
    assume \<open>z = x\<close>
    with z2 have \<open>x \<inter> {x, y} = 0\<close> by (rule subst)
    moreover from h2 have \<open>y \<in> x \<inter> {x, y}\<close> by auto
    ultimately show False by auto
  next
    assume \<open>z = y\<close>
    with z2 have \<open>y \<inter> {x, y} = 0\<close> by (rule subst)
    moreover from h1 have \<open>x \<in> y \<inter> {x, y}\<close> by auto
    ultimately show False by auto
  qed
qed

text \<open>ex 1.6: Characterizations of Transitive Sets\<close>

lemma Transset_iff_Union: \<open>Transset(x) \<longleftrightarrow> \<Union>x \<subseteq> x\<close>
proof
  assume \<open>Transset(x)\<close>
  show \<open>\<Union>x \<subseteq> x\<close>
  proof (rule subsetI)
    fix z assume \<open>z \<in> \<Union>x\<close>
    then obtain y where y1:\<open>z \<in> y\<close> and y2:\<open>y \<in> x\<close> by (erule UnionE)
    from \<open>Transset(x)\<close> and y2 have \<open>y \<subseteq> x\<close> by (unfold Transset_def, blast)
    with y1 show \<open>z \<in> x\<close> by (rule subsetD)
  qed
next
  assume \<open>\<Union>x \<subseteq> x\<close>
  show \<open>Transset(x)\<close>
  proof (unfold Transset_def, rule ballI)
    fix y assume \<open>y \<in> x\<close>
    show \<open>y \<subseteq> x\<close>
    proof (rule subsetI)
      fix z assume \<open>z \<in> y\<close>
      with \<open>y \<in> x\<close> have \<open>z \<in> \<Union>x\<close> by (rule UnionI)
      with \<open>\<Union>x \<subseteq> x\<close> show \<open>z \<in> x\<close> by (rule subsetD)
    qed
  qed
qed

lemma Transset_iff_Pow: \<open>Transset(x) \<longleftrightarrow> x \<subseteq> Pow(x)\<close>
proof
  assume \<open>Transset(x)\<close>
  show \<open>x \<subseteq> Pow(x)\<close>
  proof (rule subsetI)
    fix y assume \<open>y \<in> x\<close>
    with \<open>Transset(x)\<close> have \<open>y \<subseteq> x\<close> by (unfold Transset_def, blast)
    thus \<open>y \<in> Pow(x)\<close> by (rule PowI)
  qed
next
  assume \<open>x \<subseteq> Pow(x)\<close>
  show \<open>Transset(x)\<close>
  proof (unfold Transset_def, rule ballI)
    fix y assume \<open>y \<in> x\<close>
    with \<open>x \<subseteq> Pow(x)\<close> have \<open>y \<in> Pow(x)\<close> by (rule subsetD)
    thus \<open>y \<subseteq> x\<close> by (rule PowD)
  qed
qed

lemma Transset_Pow:
  assumes \<open>Transset(x)\<close>
  shows \<open>Transset(Pow(x))\<close>
proof (unfold Transset_def, rule ballI)
  fix y assume \<open>y \<in> Pow(x)\<close>
  hence \<open>y \<subseteq> x\<close> by (rule PowD)
  show \<open>y \<subseteq> Pow(x)\<close>
  proof (rule subsetI)
    fix z assume \<open>z \<in> y\<close>
    with \<open>y \<subseteq> x\<close> have \<open>z \<in> x\<close> by (rule subsetD)
    with assms have \<open>z \<subseteq> x\<close> by (unfold Transset_def, blast)
    thus \<open>z \<in> Pow(x)\<close> by (rule PowI)
  qed
qed

lemma Transset_Union:
  assumes \<open>\<forall>y\<in>A. Transset(y)\<close>
  shows \<open>Transset(\<Union>A)\<close>
proof (unfold Transset_def, rule ballI)
  fix z assume \<open>z \<in> \<Union>A\<close>
  then obtain y where y1:\<open>z \<in> y\<close> and y2:\<open>y \<in> A\<close> by (erule UnionE)
  from assms and y2 have \<open>Transset(y)\<close> by blast
  with y1 have \<open>z \<subseteq> y\<close> by (unfold Transset_def, blast)
  have \<open>y \<subseteq> \<Union>A\<close> using y2 by (rule Union_upper)
  with \<open>z \<subseteq> y\<close> show \<open>z \<subseteq> \<Union>A\<close> by (rule subset_trans)
qed

definition ClassInter :: \<open>(i\<Rightarrow>o)\<Rightarrow>(i\<Rightarrow>o)\<close>
  where ClassInter_def : \<open>ClassInter(P,x) == \<forall>y. P(y) \<longrightarrow> x\<in>y\<close>

definition Nat :: \<open>i\<Rightarrow>o\<close>
  where \<open>Nat == ClassInter(Ind)\<close>

lemma NatSubInf : \<open>\<And>x. Nat(x) \<Longrightarrow> x\<in>Inf\<close>
proof (unfold Nat_def)
  fix x
  assume p0:\<open>ClassInter(Ind, x)\<close>
  show \<open>x\<in>Inf\<close>
  proof -
    from p0 have \<open>\<forall>y. Ind(y) \<longrightarrow> x \<in> y\<close> by (unfold ClassInter_def)
    hence \<open>Ind(Inf) \<longrightarrow> x \<in> Inf\<close> by (rule spec)
    hence p3:\<open>Ind(Inf) \<Longrightarrow> x \<in> Inf\<close> by (rule mp)
    from IndInf show p4:\<open>x \<in> Inf\<close> by (rule p3)
  qed
qed

lemma NatSubInf' : \<open>\<forall>x. (Nat(x) \<longrightarrow> x\<in>Inf)\<close>
proof (rule allI)
  fix x from NatSubInf show \<open>(Nat(x) \<longrightarrow> x\<in>Inf)\<close> by (rule impI)
qed

definition IsTransClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsTransClass_def : \<open>IsTransClass(P) == \<forall>y. P(y) \<longrightarrow> (\<forall>z. z\<in>y \<longrightarrow> P(z))\<close>

lemma Nat0 : \<open>Nat(0)\<close>
proof -
  have \<open>\<And>y. 0 \<in> y \<and> (\<forall>ya\<in>y. succ(ya) \<in> y) \<Longrightarrow> 0 \<in> y\<close> by (erule conjE)
  hence \<open>\<And>y. Ind(y) \<Longrightarrow> 0 \<in> y\<close> by (unfold Ind_def)
  hence \<open>\<And>y. Ind(y) \<longrightarrow> 0 \<in> y\<close> by (rule impI)
  hence \<open>\<forall>y. Ind(y) \<longrightarrow> 0 \<in> y\<close> by (rule allI)
  hence \<open>ClassInter(Ind, 0)\<close> by (unfold ClassInter_def) 
  thus ?thesis by (unfold Nat_def)
qed

lemma NatSu:
  fixes x w
  assumes a:\<open>\<forall>y. Ind(y) \<longrightarrow> x \<in> y\<close>
  assumes b:\<open>Ind(w)\<close>
  shows \<open>succ(x) \<in> w\<close>
proof -
  from b have j:\<open>\<And>xa. xa \<in> w \<Longrightarrow> succ(xa) \<in> w\<close> by (rule IndE2R)
  from a have \<open>Ind(w) \<longrightarrow> x \<in> w\<close> by (rule spec)
  from this and b have \<open>x \<in> w\<close> by (rule mp)
  from \<open>x \<in> w\<close> show \<open>succ(x) \<in> w\<close> by (rule j)
qed

lemma NatSucc : \<open>\<forall>x. Nat(x) \<longrightarrow> Nat(succ(x))\<close>
proof (rule allI[OF impI])
  fix x
  assume \<open>Nat(x)\<close>
  hence \<open>ClassInter(Ind)(x)\<close> by (unfold Nat_def)
  hence \<open>\<forall>y. Ind(y) \<longrightarrow> x\<in>y\<close> by (unfold ClassInter_def)
  have \<open>\<forall>y. Ind(y) \<longrightarrow> succ(x)\<in>y\<close>
  proof (rule allI[OF impI])
    fix y
    assume \<open>Ind(y)\<close>
    with \<open>\<forall>y. Ind(y) \<longrightarrow> x\<in>y\<close> show \<open>succ(x)\<in>y\<close> by (rule NatSu)
  qed
  hence \<open>ClassInter(Ind)(succ(x))\<close> by (fold ClassInter_def)
  then show \<open>Nat(succ(x))\<close> by (fold Nat_def)
qed

definition IsIndClass :: \<open>(i\<Rightarrow>o)\<Rightarrow>o\<close>
  where IsIndClass_def : \<open>IsIndClass(P) == P(0) \<and> (\<forall>y. P(y) \<longrightarrow> P(succ(y)))\<close>

lemma NatIsInd : \<open>IsIndClass(Nat)\<close>
proof (unfold IsIndClass_def)
  from Nat0 and NatSucc 
  show \<open>Nat(0) \<and> (\<forall>y. Nat(y) \<longrightarrow> Nat(succ(y)))\<close> by (rule conjI)
qed

definition Omega :: \<open>i\<close>
  where Omega_def : \<open>Omega == { y \<in> Inf . Nat(y) }\<close>

lemma NatSubOmega : \<open>\<And>x. Nat(x) \<Longrightarrow> x \<in> Omega\<close>
proof -
  fix x
  assume \<open>Nat(x)\<close>
  hence \<open>x \<in> Inf\<close> by (rule NatSubInf)
  from \<open>x \<in> Inf\<close> and \<open>Nat(x)\<close> have \<open>x \<in> {x\<in>Inf. Nat(x)}\<close> by (rule CollectI)
  thus \<open>x \<in> Omega\<close> by (fold Omega_def)
qed

text \<open>ex 1.7: Image of Union\<close>

lemma image_Union : \<open>r `` (\<Union>A) = (\<Union>x\<in>A. r `` x)\<close>
proof (rule equalityI)
  show \<open>r `` (\<Union>A) \<subseteq> (\<Union>x\<in>A. r `` x)\<close>
  proof (rule subsetI)
    fix x assume a1:\<open>x \<in> r `` (\<Union>A)\<close>
    then obtain xa where b1:\<open>xa \<in> \<Union>A\<close> and b2:\<open>\<langle>xa, x\<rangle> \<in> r\<close>
      unfolding image_def by blast
    from b1 obtain y where q1:\<open>xa \<in> y\<close> and q2:\<open>y \<in> A\<close> by (rule UnionE)
    from b2 and q1 have c1:\<open>x \<in> r `` y\<close> by (rule imageI)
    with q2 show \<open>x \<in> (\<Union>x\<in>A. r `` x)\<close> by (rule UN_I)
  qed
next
  show \<open>(\<Union>x\<in>A. r `` x) \<subseteq> r `` (\<Union>A)\<close>
  proof (rule subsetI)
    fix x assume a0:\<open>x \<in> (\<Union>x\<in>A. r `` x)\<close>
    then obtain y where y1:\<open>y \<in> A\<close> and y2:\<open>x \<in> r `` y\<close> by (rule UN_E)
    then obtain xa where xa1:\<open>\<langle>xa, x\<rangle> \<in> r\<close> and xa2:\<open>xa \<in> y\<close>
      unfolding image_def by blast
    from y1 and xa2 have \<open>xa \<in> \<Union>A\<close> by (rule UnionI)
    with xa1 show \<open>x \<in> r `` (\<Union>A)\<close> by (rule imageI)
  qed
qed

section \<open>Jech Chapter 2: Ordinals\<close>

lemma Ord_0: \<open>Ord(0)\<close>
  by (rule Ord_0)

lemma Ord_succ: \<open>Ord(\<alpha>) \<Longrightarrow> Ord(succ(\<alpha>))\<close>
  by (rule Ord_succ)

lemma Ord_in_Ord: \<open>\<alpha> \<in> \<beta> \<Longrightarrow> Ord(\beta) \<Longrightarrow> Ord(\<alpha>)\<close>
  by (rule Ord_in_Ord)

lemma Ord_trichotomy:
  assumes \<open>Ord(\<alpha>)\<close> and \<open>Ord(\<beta>)\<close>
  shows \<open>\<alpha> \<in> \<beta> \<or> \<alpha> = \<beta> \<or> \<beta> \<in> \<alpha>\<close>
proof -
  from assms have \<open>\<alpha> < \<beta> \<or> \<alpha> = \<beta> \<or> \<beta> < \<alpha>\<close> by (rule Ord_linear)
  thus ?thesis by (auto simp add: lt_def)
qed

lemma Ord_Union:
  assumes \<open>\<forall>x\<in>A. Ord(x)\<close>
  shows \<open>Ord(\<Union>A)\<close>
  using assms by (rule Ord_Union)

lemma Transset_trans_Memrel:
  assumes \<open>\<forall>j\<in>i. Transset(j)\<close>
  shows \<open>trans(Memrel(i))\<close>
  using assms by (unfold Transset_def trans_def, blast)

lemma transfinite_induction_principle:
  assumes \<open>Ord(\<alpha>)\<close>
      and \<open>P(0)\<close>
      and \<open>\<And>x. Ord(x) \<Longrightarrow> P(x) \<Longrightarrow> P(succ(x))\<close>
      and \<open>\<And>x. Limit(x) \<Longrightarrow> (\<forall>y\<in>x. P(y)) \<Longrightarrow> P(x)\<close>
  shows \<open>P(\<alpha>)\<close>
  using assms by (rule transfinite_induct)

end
